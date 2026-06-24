use std::collections::{HashMap, HashSet};
use std::fs;

use bumpalo::Bump;

use crate::backend::ir::FunSig;
use crate::checker::TypeChecker;
use crate::checker::context::empty_ctx;
use crate::checker::erase::Eraser;
use crate::core::eval::Evaluator;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Term};

/// Result of collecting variant constructor args: (union_name, variant_index, field_specs, args).
type VariantWithArgs<'bump> = (
    Name<'bump>,
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    Vec<&'bump Term<'bump>>,
);

/// Result of collecting struct constructor args: (struct_name, field_specs, args).
type StructWithArgs<'bump> = (
    Name<'bump>,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    Vec<&'bump Term<'bump>>,
);
use crate::diagnostic::Diagnostic;
use crate::front::parser::{TopLevel, parse_expr_top, parse_program};
use crate::pretty::PrettyPrinter;

/// The compiler orchestrator — owns the bump allocator, term arena, and
/// coordinates parsing, type checking, and evaluation.
///
/// This struct bundles all compilation state together instead of threading
/// it through free functions.
pub struct Compiler<'bump> {
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
    checker: TypeChecker<'bump>,
    /// Environment: maps top-level names to their desugared defining terms.
    env: HashMap<&'bump str, &'bump Term<'bump>>,
    /// Accumulated top-level items (for code generation).
    pub tops: Vec<TopLevel<'bump>>,
    /// Raw (un-erased) function definitions for on-demand codegen.
    /// Bodies are resolved & desugared, but type params are NOT erased yet.
    raw_defs: Vec<TopLevel<'bump>>,
    /// Function signatures extracted before erasure (for C codegen).
    fun_sigs: Vec<(&'bump str, FunSig)>,
    /// Union type definitions collected before erasure (for C codegen).
    pub union_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    /// Struct type definitions collected before erasure (for C codegen).
    pub struct_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    /// Suppress diagnostic output (set during codegen).
    quiet: bool,
}

impl<'bump> Compiler<'bump> {
    pub fn new(bump: &'bump Bump, arena: &'bump TermArena<'bump>) -> Self {
        Self {
            bump,
            arena,
            checker: TypeChecker::new(arena),
            env: HashMap::new(),
            tops: vec![],
            raw_defs: vec![],
            fun_sigs: vec![],
            union_types: vec![],
            struct_types: vec![],
            quiet: false,
        }
    }

    /// Process a source file: parse it and handle each top-level item.
    pub fn process_file(&mut self, file: &str) -> Result<(), Diagnostic> {
        let content =
            fs::read_to_string(file).map_err(|e| Diagnostic::new(format!("{}: {}", file, e)))?;
        self.process_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn process_file_str(&mut self, source: &str) -> Result<(), Diagnostic> {
        self.process_str(source, "<str>")
    }

    fn process_str(&mut self, content: &str, file: &str) -> Result<(), Diagnostic> {
        let tops = parse_program(content, self.bump, self.arena).map_err(|e| {
            Diagnostic::with_span(format!("{}: parse error: {}", file, e.message), e.span)
        })?;
        for top in tops {
            self.process_top_level(top, file)?;
        }
        Ok(())
    }

    /// Process a source file, collect top-level items, and type-check.
    pub fn collect_file(&mut self, file: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        let content =
            fs::read_to_string(file).map_err(|e| Diagnostic::new(format!("{}: {}", file, e)))?;
        self.collect_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn collect_file_str(&mut self, source: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        self.collect_str(source, "<str>")
    }

    fn collect_str(&mut self, content: &str, file: &str) -> Result<(), Diagnostic> {
        let tops = parse_program(content, self.bump, self.arena).map_err(|e| {
            Diagnostic::with_span(format!("{}: parse error: {}", file, e.message), e.span)
        })?;
        for top in &tops {
            self.process_top_level(top.clone(), file)?;
        }
        let (union_names, struct_names) = self.build_name_sets(&tops);
        self.collect_signatures(&tops, &union_names, &struct_names)?;

        // Build raw (un-erased) definitions for on-demand codegen.
        // Bodies are resolved from env and desugared, but type params remain.
        let desugarer = crate::core::debruijn::Desugarer::new(self.arena);
        for top in &tops {
            if let TopLevel::TLDef(name, params, m_ret, body_term, span) = top {
                // Skip union/struct typedefs — they are emitted by type-emission pass
                if matches!(body_term, Term::UnionDef(..) | Term::StructDef(..)) {
                    continue;
                }
                let term = self.env.get(name).copied().unwrap_or(*body_term);
                let resolved = self.subst_top_level(term);
                let desugared = desugarer.desugar(resolved);
                self.raw_defs.push(TopLevel::TLDef(
                    name,
                    params,
                    *m_ret,
                    desugared,
                    span.clone(),
                ));
            }
        }

        let eraser = Eraser::new(self.arena);
        let evald_tops = self.erase_and_collect_tops(tops, &eraser);
        self.tops.extend(evald_tops);
        Ok(())
    }

    /// Build sets of union and struct type names from the top-level definitions.
    /// These are used by the C backend to emit correct parameter and return types.
    fn build_name_sets(&self, tops: &[TopLevel<'bump>]) -> (HashSet<String>, HashSet<String>) {
        let union_names: HashSet<String> = tops
            .iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(name, _, _, Term::UnionDef(..), _) => Some(name.to_string()),
                _ => None,
            })
            .collect();
        let struct_names: HashSet<String> = tops
            .iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(name, _, _, Term::StructDef(..), _) => Some(name.to_string()),
                _ => None,
            })
            .collect();
        (union_names, struct_names)
    }

    /// Collect function signatures, union types, and struct types from the
    /// original (un-erased) top-level definitions before erasure.
    fn collect_signatures(
        &mut self,
        tops: &[TopLevel<'bump>],
        union_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<(), Diagnostic> {
        for top in tops {
            if let TopLevel::TLDef(name, params, m_ret, body, _) = top {
                if matches!(body, Term::UnionDef(..)) {
                    self.union_types.push((name, body));
                } else if matches!(body, Term::StructDef(..)) {
                    self.struct_types.push((name, body));
                }
                // Collect FunSig for non-type definitions (functions, constants).
                // Generic type constructors (params + UnionDef/StructDef) are
                // compile-time entities — skip FunSig for them.
                if !matches!(body, Term::UnionDef(..) | Term::StructDef(..)) {
                    let sig = FunSig::from_func(params, *m_ret, body, union_names, struct_names)
                        .map_err(Diagnostic::new)?;
                    self.fun_sigs.push((name, sig));
                }
            }
        }
        Ok(())
    }

    /// Erase, resolve, and filter top-level definitions. Skips union/struct
    /// typedefs (including generic ones) and drops zero-param type aliases after erasure.
    fn erase_and_collect_tops(
        &self,
        tops: Vec<TopLevel<'bump>>,
        eraser: &Eraser<'bump>,
    ) -> Vec<TopLevel<'bump>> {
        tops.into_iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(_name, _params, _m_ret, Term::UnionDef(..) | Term::StructDef(..), _) =>
                {
                    None
                }
                TopLevel::TLDef(name, params, m_ret, body_term, span) => {
                    let term = self.env.get(name).copied().unwrap_or(body_term);
                    let resolved = self.subst_top_level(term);
                    let desugared = self.checker.desugarer.desugar(resolved);
                    let erased = eraser.erase(desugared);
                    Some(TopLevel::TLDef(name, params, m_ret, erased, span))
                }
                TopLevel::TLShow(term, span) | TopLevel::TLExpr(term, span) => {
                    let resolved = self.subst_top_level(term);
                    let desugared = self.checker.desugarer.desugar(resolved);
                    Some(TopLevel::TLShow(eraser.erase(desugared), span))
                }
                TopLevel::TLTheorem(name, _, body, span) => {
                    let resolved_body = self.subst_top_level(body);
                    let desugared = self.checker.desugarer.desugar(resolved_body);
                    let erased = eraser.erase(desugared);
                    Some(TopLevel::TLDef(name, &[], None, erased, span))
                }
                TopLevel::TLCheck(_, _, _) => None,
            })
            .filter(|top| {
                !matches!(
                    top,
                    TopLevel::TLDef(_, params, _, body, _)
                        if params.is_empty()
                            && matches!(body, Term::Builtin(_) | Term::Named(_) | Term::UnionDef(..) | Term::StructDef(..))
                )
            })
            .collect()
    }

    /// Evaluate an expression string (for `--eval`).
    pub fn eval_expr(&self, expr: &str) -> Result<(), Diagnostic> {
        let term = parse_expr_top(expr, self.bump, self.arena).map_err(|err| {
            Diagnostic::with_span(format!("--eval parse error: {}", err.message), err.span)
        })?;
        let resolved = self.resolve_all(term);
        let self_name = self.extract_func_name(term);
        let mut ev = Evaluator::new(self.arena);
        if let Some(n) = self_name {
            ev.set_self_name(n);
        }
        match ev.eval(resolved) {
            Err(err) => Err(Diagnostic::new(format!("--eval error: {}", err))),
            Ok(val) => {
                println!("{}", PrettyPrinter::pretty(val));
                Ok(())
            }
        }
    }

    /// Get the collected top-level items (for code generation).
    pub fn tops(&self) -> &[TopLevel<'bump>] {
        &self.tops
    }

    /// Get un-erased function definitions (for on-demand codegen).
    pub fn raw_defs(&self) -> &[TopLevel<'bump>] {
        &self.raw_defs
    }

    /// Get the function signatures extracted before erasure (for C codegen).
    pub fn fun_sigs(&self) -> &[(&'bump str, FunSig)] {
        &self.fun_sigs
    }

    // ── private helpers ──

    /// Desugar a generic union/struct definition (one with type parameters)
    /// into `Annot(Lam(...), Pi(...))` for env storage.
    fn desugar_top_def(
        &self,
        _name: Name<'bump>,
        params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let func_body = params.iter().rfold(body, |b, &(_pn, _)| self.arena.lam(b));
        let default = self.arena.builtin(self.arena.alloc_str("data"));
        let func_type = params
            .iter()
            .rfold(m_ret.unwrap_or(default), |b, &(pn, mc)| {
                self.arena.pi(pn, mc.unwrap_or(default), b)
            });
        self.arena.annot(func_body, func_type)
    }

    /// Process a single top-level item.
    fn process_top_level(&mut self, top: TopLevel<'bump>, file: &str) -> Result<(), Diagnostic> {
        match top {
            TopLevel::TLDef(name, params, _m_ret, body, _span) => {
                if matches!(body, Term::UnionDef(..)) {
                    if !self.quiet {
                        println!("[union] {}", name);
                    }
                    let type_param_names: Vec<_> = params.iter().map(|(n, _)| *n).collect();
                    let type_params = self.arena.alloc_slice(&type_param_names);
                    self.checker.add_union(name, body, type_params);
                    if !params.is_empty() {
                        // Generic union: desugar and add to env
                        let term = self.desugar_top_def(name, params, _m_ret, body);
                        self.env.insert(name, term);
                    }
                } else if matches!(body, Term::StructDef(..)) {
                    if !self.quiet {
                        println!("[struct] {}", name);
                    }
                    let type_param_names: Vec<_> = params.iter().map(|(n, _)| *n).collect();
                    let type_params = self.arena.alloc_slice(&type_param_names);
                    self.checker.add_struct(name, body, type_params);
                    if !params.is_empty() {
                        // Generic struct: desugar and add to env
                        let term = self.desugar_top_def(name, params, _m_ret, body);
                        self.env.insert(name, term);
                    }
                } else if params.is_empty() && matches!(body, Term::Refine(_, _, _)) {
                    let Term::Refine(_, parent, predicate) = body else {
                        unreachable!()
                    };
                    if !self.quiet {
                        println!("[refinement] {}", name);
                    }
                    self.checker.add_refinement(name, parent, predicate);
                } else {
                    // Body is already desugared (Annot(Lam(...), Pi(...)))
                    if !self.quiet {
                        println!("[defined] {}", name);
                    }
                    self.env.insert(name, body);
                }
            }
            TopLevel::TLCheck(term, constraint, span) => {
                let resolved = self.resolve_all(term);
                let resolved_constraint = self.resolve_all(constraint);
                match self
                    .checker
                    .check(&empty_ctx(), resolved, resolved_constraint)
                {
                    Err(err) => {
                        return Err(Diagnostic::with_span(
                            format!("{}: check failed: {}", file, err),
                            span,
                        ));
                    }
                    Ok(_) => {
                        if !self.quiet {
                            println!("[OK]");
                        }
                    }
                }
            }
            TopLevel::TLTheorem(name, prop, body, span) => {
                let resolved_body = self.resolve_all(body);
                let resolved_prop = self.resolve_all(prop);
                match self
                    .checker
                    .check(&empty_ctx(), resolved_body, resolved_prop)
                {
                    Err(err) => {
                        return Err(Diagnostic::with_span(
                            format!("{}: theorem check failed: {}", file, err),
                            span,
                        ));
                    }
                    Ok(_) => {
                        if !self.quiet {
                            println!("[theorem] {}", name);
                        }
                        // Desugar NamedLam → Lam before storing in env
                        let desugarer = crate::core::debruijn::Desugarer::new(self.arena);
                        self.env.insert(name, desugarer.desugar(body));
                    }
                }
            }
            TopLevel::TLShow(_term, _span) => {
                if self.quiet {
                    return Ok(()); // codegen handles #show separately
                }
                let resolved = self.resolve_all(_term);
                let self_name = self.extract_func_name(_term);
                let mut ev = Evaluator::new(self.arena);
                if let Some(n) = self_name {
                    ev.set_self_name(n);
                }
                match ev.eval(resolved) {
                    Err(err) => eprintln!("{}: show error: {}", file, err),
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
            TopLevel::TLExpr(_term, _span) => {
                if self.quiet {
                    return Ok(()); // codegen handles #expr separately
                }
                let resolved = self.resolve_all(_term);
                let self_name = self.extract_func_name(_term);
                let mut ev = Evaluator::new(self.arena);
                if let Some(n) = self_name {
                    ev.set_self_name(n);
                }
                match ev.eval(resolved) {
                    Err(err) => eprintln!("{}: eval error: {}", file, err),
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
        }
        Ok(())
    }

    /// Resolve ALL `Builtin(name)` references from the env (constants AND functions).
    /// Used for eval paths where function bodies need to be available.
    /// Also runs the desugar pass to convert `NamedLam` → `Lam` and `Named` → `Var`.
    fn resolve_all(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Named(name) = t
                && let Some(def) = self.env.get(name)
            {
                return Some(def);
            }
            None
        });
        // Also resolve variant apps, struct constructors, and zero-arg constructors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        let t = self.arena.map(t, &|t| {
            if let Term::Builtin(name) | Term::Named(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
                    && field_specs.is_empty()
                {
                    return Some(self.arena.variant(uname, idx, &[]));
                }
                // Zero-arg struct constructor
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
                    && fields.is_empty()
                {
                    return Some(self.arena.struct_cons(sname, &[]));
                }
                // Struct projector
                if let Some(_idx) = self.checker.lookup_struct_proj(name) {
                    // Can't resolve without subject — leave as-is
                }
            }
            None
        });
        // Desugar: convert NamedLam → Lam, resolve Named → Var
        let desugarer = crate::core::debruijn::Desugarer::new(self.arena);
        desugarer.desugar(t)
    }

    /// Extract the function name from a term if it's a recursive call.
    /// Only returns `Some(name)` if the head is a `Builtin(name)` that
    /// maps to a function (i.e., has `Lam` body) in the env.
    fn extract_func_name(&self, term: &'bump Term<'bump>) -> Option<Name<'bump>> {
        let mut head = term;
        while let Term::App(f, _) = head {
            head = f;
        }
        if let Term::Builtin(name) | Term::Named(name) = head
            && let Some(def) = self.env.get(name)
        {
            if def.is_constant() {
                return None; // constants don't need self-reference
            }
            return Some(name);
        }
        None
    }

    /// Substitute known top-level definitions into a term (O(1) lookup).
    /// Also resolves variant/struct constructors to their term forms.
    /// Uses `is_constant()` to distinguish constants from functions.
    fn subst_top_level(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // First pass: resolve env lookups for constants only
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Named(name) = t
                && let Some(def) = self.env.get(name)
                && def.is_constant()
            {
                return Some(def);
            }
            None
        });
        // Second pass: resolve variant apps, struct constructors, and projectors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        // Third pass: resolve remaining zero-arg variant/struct constructors
        self.arena.map(t, &|t| {
            if let Term::Builtin(name) | Term::Named(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
                    && field_specs.is_empty()
                {
                    return Some(self.arena.variant(uname, idx, &[]));
                }
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
                    && fields.is_empty()
                {
                    return Some(self.arena.struct_cons(sname, &[]));
                }
            }
            None
        })
    }

    /// Convert `App*(Builtin(name), args...)` to `Variant(union, idx, args)`.
    fn resolve_variant_apps(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // Try top-level first
        if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(t)
            && args.len() == field_specs.len()
        {
            let v = self
                .arena
                .variant(uname, idx, self.arena.alloc_slice(&args));
            // Recurse into payload to resolve nested constructors
            return self.resolve_variant_apps(v);
        }
        self.arena.map(t, &|node| {
            if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(node)
                && args.len() == field_specs.len()
            {
                let v = self
                    .arena
                    .variant(uname, idx, self.arena.alloc_slice(&args));
                return Some(self.resolve_variant_apps(v));
            }
            None
        })
    }

    /// Unwrap an App chain to find a variant constructor and collect its args.
    fn collect_variant_args(&self, t: &'bump Term<'bump>) -> Option<VariantWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Named(name) = current
            && let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
        {
            return Some((uname, idx, field_specs, args));
        }
        None
    }

    /// Convert `App*(Named("name.mk"), args...)` to `StructCons(name, args)`.
    fn resolve_struct_ctors(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Some((sname, field_specs, args)) = self.collect_struct_args(t)
            && args.len() == field_specs.len()
        {
            let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
            return self.resolve_struct_ctors(sc);
        }
        self.arena.map(t, &|node| {
            if let Some((sname, field_specs, args)) = self.collect_struct_args(node)
                && args.len() == field_specs.len()
            {
                let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
                return Some(self.resolve_struct_ctors(sc));
            }
            None
        })
    }

    /// Unwrap an App chain to find a struct constructor (Name.mk) and collect its args.
    fn collect_struct_args(&self, t: &'bump Term<'bump>) -> Option<StructWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Named(name) = current
            && let Some((sname, field_specs)) = self.checker.lookup_struct_ctor(name)
        {
            return Some((sname, field_specs, args));
        }
        None
    }

    /// Convert `App(Builtin("Name.field"), arg)` to `StructProj(arg, idx)`.
    fn resolve_struct_projs(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::App(f, arg) = node
                && let Term::Builtin(name) | Term::Named(name) = f
                && let Some(idx) = self.checker.lookup_struct_proj(name)
            {
                return Some(self.arena.struct_proj(arg, idx));
            }
            None
        })
    }
}
