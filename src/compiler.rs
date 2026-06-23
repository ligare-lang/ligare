use std::collections::HashMap;
use std::fs;

use bumpalo::Bump;

use crate::backend::ir::FunSig;
use crate::checker::TypeChecker;
use crate::checker::context::empty_ctx;
use crate::checker::erase::Eraser;
use crate::core::eval::Evaluator;
use crate::core::pool::TermArena;
use crate::core::syntax::{FuncDef, Name, Term};
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
            fun_sigs: vec![],
            union_types: vec![],
            struct_types: vec![],
            quiet: false,
        }
    }

    /// Process a source file: parse it and handle each top-level item.
    pub fn process_file(&mut self, file: &str) -> Result<(), String> {
        let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
        self.process_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn process_file_str(&mut self, source: &str) -> Result<(), String> {
        self.process_str(source, "<str>")
    }

    fn process_str(&mut self, content: &str, file: &str) -> Result<(), String> {
        let tops = parse_program(&content, self.bump, self.arena)
            .map_err(|e| format!("{}: parse error: {}", file, e))?;
        for top in tops {
            self.process_top_level(top, file)?;
        }
        Ok(())
    }

    /// Process a source file, collect top-level items, and type-check.
    pub fn collect_file(&mut self, file: &str) -> Result<(), String> {
        self.quiet = true;
        let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
        self.collect_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn collect_file_str(&mut self, source: &str) -> Result<(), String> {
        self.quiet = true;
        self.collect_str(source, "<str>")
    }

    fn collect_str(&mut self, content: &str, file: &str) -> Result<(), String> {
        let tops = parse_program(&content, self.bump, self.arena)
            .map_err(|e| format!("{}: parse error: {}", file, e))?;
        for top in &tops {
            self.process_top_level(*top, file)?;
        }
        // Extract function signatures from the original (un-erased) FuncDef
        // so the C backend can emit correct parameter and return types.
        let union_names: std::collections::HashSet<String> = tops
            .iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(name, fd)
                    if fd.params.is_empty() && matches!(fd.body, Term::UnionDef(..)) =>
                {
                    Some(name.to_string())
                }
                _ => None,
            })
            .collect();
        let struct_names: std::collections::HashSet<String> = tops
            .iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(name, fd)
                    if fd.params.is_empty() && matches!(fd.body, Term::StructDef(..)) =>
                {
                    Some(name.to_string())
                }
                _ => None,
            })
            .collect();
        for top in &tops {
            match top {
                TopLevel::TLDef(name, func_def) => {
                    // Collect union types for C codegen
                    if func_def.params.is_empty() && matches!(func_def.body, Term::UnionDef(..)) {
                        self.union_types.push((name, func_def.body));
                    } else if func_def.params.is_empty()
                        && matches!(func_def.body, Term::StructDef(..))
                    {
                        self.struct_types.push((name, func_def.body));
                    } else {
                        let sig = FunSig::from_func(
                            func_def.params,
                            func_def.ret,
                            func_def.body,
                            &union_names,
                            &struct_names,
                        )?;
                        self.fun_sigs.push((name, sig));
                    }
                }
                _ => {}
            }
        }
        let eraser = Eraser::new(self.arena);
        let evald_tops: Vec<TopLevel<'bump>> = tops
            .into_iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(_name, func_def)
                    if func_def.params.is_empty()
                        && (matches!(func_def.body, Term::UnionDef(..))
                            || matches!(func_def.body, Term::StructDef(..))) =>
                {
                    None // Skip union/struct type definitions (emitted as typedefs)
                }
                TopLevel::TLDef(name, _func_def) => {
                    // Use the already-desugared term from env (set by process_top_level)
                    // instead of re-desugaring from the original FuncDef.
                    let term = self
                        .env
                        .get(name)
                        .copied()
                        .unwrap_or_else(|| self.arena.desugar_func_def(_func_def));
                    let resolved = self.subst_top_level(term);
                    let erased = eraser.erase(resolved);
                    let erased_func_def = FuncDef {
                        name,
                        params: _func_def.params,
                        ret: _func_def.ret,
                        body: erased,
                    };
                    Some(TopLevel::TLDef(
                        name,
                        self.arena.bump().alloc(erased_func_def),
                    ))
                }
                TopLevel::TLShow(term) | TopLevel::TLExpr(term) => {
                    let resolved = self.subst_top_level(term);
                    Some(TopLevel::TLShow(eraser.erase(resolved)))
                }
                TopLevel::TLTheorem(name, _, body) => {
                    let resolved_body = self.subst_top_level(body);
                    let erased = eraser.erase(resolved_body);
                    let func_def = FuncDef {
                        name,
                        params: &[],
                        ret: None,
                        body: erased,
                    };
                    Some(TopLevel::TLDef(name, self.arena.bump().alloc(func_def)))
                }
                TopLevel::TLCheck(_, _) => None,
            })
            // Drop zero-param definitions that are type aliases
            // (bare builtins or union/struct defs with empty body after erasure).
            .filter(|top| {
                !matches!(
                    top,
                    TopLevel::TLDef(_, FuncDef { params, body, .. })
                        if params.is_empty()
                            && matches!(body, Term::Builtin(_) | Term::UnionDef(..) | Term::StructDef(..))
                )
            })
            .collect();
        self.tops.extend(evald_tops);
        Ok(())
    }

    /// Evaluate an expression string (for `--eval`).
    pub fn eval_expr(&self, expr: &str) -> Result<(), String> {
        let term = parse_expr_top(expr, self.bump, self.arena)
            .map_err(|err| format!("--eval parse error: {}", err))?;
        let resolved = self.resolve_all(term);
        let self_name = self.extract_func_name(term);
        let mut ev = Evaluator::new(self.arena);
        if let Some(n) = self_name {
            ev.set_self_name(n);
        }
        match ev.eval(resolved) {
            Err(err) => Err(format!("--eval error: {}", err)),
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

    /// Get the function signatures extracted before erasure (for C codegen).
    pub fn fun_sigs(&self) -> &[(&'bump str, FunSig)] {
        &self.fun_sigs
    }

    // ── private helpers ──

    /// Process a single top-level item.
    fn process_top_level(&mut self, top: TopLevel<'bump>, file: &str) -> Result<(), String> {
        match top {
            TopLevel::TLDef(name, func_def) => {
                // parse_def always wraps the body in a FuncDef.
                // For zero-parameter definitions whose body is a
                // refinement, extract the Refine so it is properly
                // registered in the constraint table.
                if func_def.params.is_empty() && matches!(func_def.body, Term::UnionDef(..)) {
                    if !self.quiet {
                        println!("[union] {}", name);
                    }
                    self.checker.add_union(name, func_def.body);
                } else if func_def.params.is_empty() && matches!(func_def.body, Term::StructDef(..))
                {
                    if !self.quiet {
                        println!("[struct] {}", name);
                    }
                    self.checker.add_struct(name, func_def.body);
                } else if func_def.params.is_empty()
                    && matches!(func_def.body, Term::Refine(_, _, _))
                {
                    let Term::Refine(_, parent, predicate) = func_def.body else {
                        unreachable!()
                    };
                    if !self.quiet {
                        println!("[refinement] {}", name);
                    }
                    self.checker.add_refinement(name, parent, predicate);
                } else {
                    let term = self.arena.desugar_func_def(func_def);
                    if !self.quiet {
                        println!("[defined] {}", name);
                    }
                    self.env.insert(name, term);
                }
            }
            TopLevel::TLCheck(term, constraint) => {
                let resolved = self.resolve_all(term);
                let resolved_constraint = self.resolve_all(constraint);
                match self
                    .checker
                    .check(&empty_ctx(), resolved, resolved_constraint)
                {
                    Err(err) => return Err(format!("{}: check failed: {}", file, err)),
                    Ok(_) => {
                        if !self.quiet {
                            println!("[OK]");
                        }
                    }
                }
            }
            TopLevel::TLTheorem(name, prop, body) => {
                let resolved_body = self.resolve_all(body);
                let resolved_prop = self.resolve_all(prop);
                match self
                    .checker
                    .check(&empty_ctx(), resolved_body, resolved_prop)
                {
                    Err(err) => return Err(format!("{}: theorem check failed: {}", file, err)),
                    Ok(_) => {
                        if !self.quiet {
                            println!("[theorem] {}", name);
                        }
                        self.env.insert(name, body);
                    }
                }
            }
            TopLevel::TLShow(_term) => {
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
            TopLevel::TLExpr(_term) => {
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
    fn resolve_all(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) = t {
                if let Some(def) = self.env.get(name) {
                    return Some(def);
                }
            }
            None
        });
        // Also resolve variant apps, struct constructors, and zero-arg constructors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        self.arena.map(t, &|t| {
            if let Term::Builtin(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name) {
                    if field_specs.is_empty() {
                        return Some(self.arena.variant(uname, idx, &[]));
                    }
                }
                // Zero-arg struct constructor
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name) {
                    if fields.is_empty() {
                        return Some(self.arena.struct_cons(sname, &[]));
                    }
                }
                // Struct projector
                if let Some(_idx) = self.checker.lookup_struct_proj(name) {
                    // Can't resolve without subject — leave as-is
                }
            }
            None
        })
    }

    /// Extract the function name from a term if it's a recursive call.
    /// Only returns `Some(name)` if the head is a `Builtin(name)` that
    /// maps to a function (i.e., has `Lam` body) in the env.
    fn extract_func_name(&self, term: &'bump Term<'bump>) -> Option<Name<'bump>> {
        let mut head = term;
        while let Term::App(f, _) = head {
            head = f;
        }
        if let Term::Builtin(name) = head {
            if let Some(def) = self.env.get(name) {
                if def.is_constant() {
                    return None; // constants don't need self-reference
                }
                return Some(name);
            }
        }
        None
    }

    /// Substitute known top-level definitions into a term (O(1) lookup).
    /// Also resolves variant/struct constructors to their term forms.
    /// Uses `is_constant()` to distinguish constants from functions.
    fn subst_top_level(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // First pass: resolve env lookups for constants only
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) = t {
                if let Some(def) = self.env.get(name) {
                    if def.is_constant() {
                        return Some(def);
                    }
                }
            }
            None
        });
        // Second pass: resolve variant apps, struct constructors, and projectors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        // Third pass: resolve remaining zero-arg variant/struct constructors
        self.arena.map(t, &|t| {
            if let Term::Builtin(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name) {
                    if field_specs.is_empty() {
                        return Some(self.arena.variant(uname, idx, &[]));
                    }
                }
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name) {
                    if fields.is_empty() {
                        return Some(self.arena.struct_cons(sname, &[]));
                    }
                }
            }
            None
        })
    }

    /// Convert `App*(Builtin(name), args...)` to `Variant(union, idx, args)`.
    fn resolve_variant_apps(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // Try top-level first
        if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(t) {
            if args.len() == field_specs.len() {
                let v = self
                    .arena
                    .variant(uname, idx, self.arena.alloc_slice(&args));
                // Recurse into payload to resolve nested constructors
                return self.resolve_variant_apps(v);
            }
        }
        self.arena.map(t, &|node| {
            if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(node) {
                if args.len() == field_specs.len() {
                    let v = self
                        .arena
                        .variant(uname, idx, self.arena.alloc_slice(&args));
                    return Some(self.resolve_variant_apps(v));
                }
            }
            None
        })
    }

    /// Unwrap an App chain to find a variant constructor and collect its args.
    fn collect_variant_args(
        &self,
        t: &'bump Term<'bump>,
    ) -> Option<(
        Name<'bump>,
        usize,
        &'bump [(Name<'bump>, &'bump Term<'bump>)],
        Vec<&'bump Term<'bump>>,
    )> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        loop {
            if let Term::App(f, a) = current {
                args.push(*a);
                current = f;
            } else {
                break;
            }
        }
        args.reverse();
        if let Term::Builtin(name) = current {
            if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name) {
                return Some((uname, idx, field_specs, args));
            }
        }
        None
    }

    /// Convert `App*(Builtin("name.mk"), args...)` to `StructCons(name, args)`.
    fn resolve_struct_ctors(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Some((sname, field_specs, args)) = self.collect_struct_args(t) {
            if args.len() == field_specs.len() {
                let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
                return self.resolve_struct_ctors(sc);
            }
        }
        self.arena.map(t, &|node| {
            if let Some((sname, field_specs, args)) = self.collect_struct_args(node) {
                if args.len() == field_specs.len() {
                    let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
                    return Some(self.resolve_struct_ctors(sc));
                }
            }
            None
        })
    }

    /// Unwrap an App chain to find a struct constructor (Name.mk) and collect its args.
    fn collect_struct_args(
        &self,
        t: &'bump Term<'bump>,
    ) -> Option<(
        Name<'bump>,
        &'bump [(Name<'bump>, &'bump Term<'bump>)],
        Vec<&'bump Term<'bump>>,
    )> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        loop {
            if let Term::App(f, a) = current {
                args.push(*a);
                current = f;
            } else {
                break;
            }
        }
        args.reverse();
        if let Term::Builtin(name) = current {
            if let Some((sname, field_specs)) = self.checker.lookup_struct_ctor(name) {
                return Some((sname, field_specs, args));
            }
        }
        None
    }

    /// Convert `App(Builtin("Name.field"), arg)` to `StructProj(arg, idx)`.
    fn resolve_struct_projs(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::App(f, arg) = node {
                if let Term::Builtin(name) = f {
                    if let Some(idx) = self.checker.lookup_struct_proj(name) {
                        return Some(self.arena.struct_proj(arg, idx));
                    }
                }
            }
            None
        })
    }
}
