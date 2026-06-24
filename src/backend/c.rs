//! C code generation backend.
//!
//! Generates straightforward C from erased `Term` trees.  C type
//! inference happens directly during emission via a `var_types` stack
//! that mirrors De Bruijn binding structure.

use crate::backend::ir::{CType, FunSig, constraint_to_ctype, is_type_universe};
use crate::core::syntax::{Name, PrimOp, Term};
use crate::front::parser::TopLevel;
use std::collections::{HashMap, HashSet};

/// C keywords that conflict with Ligare identifiers.
const C_KEYWORDS: &[&str] = &[
    "auto",
    "break",
    "case",
    "char",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extern",
    "float",
    "for",
    "goto",
    "if",
    "int",
    "long",
    "register",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "struct",
    "switch",
    "typedef",
    "union",
    "unsigned",
    "void",
    "volatile",
    "while",
    "_Bool",
    "_Complex",
    "_Imaginary",
];

/// Escape a name if it conflicts with a C keyword.
fn escape_c_name(name: &str) -> String {
    if C_KEYWORDS.contains(&name) {
        format!("_{name}")
    } else {
        name.to_string()
    }
}

/// Info about a union variant for C codegen.
#[allow(dead_code)]
struct VariantInfo {
    name: String,
    fields: Vec<(String, CType)>,
}

/// Union type info for C codegen.
#[allow(dead_code)]
struct UnionInfo {
    variants: Vec<VariantInfo>,
}

/// Struct type info for C codegen.
struct StructInfo {
    fields: Vec<(String, CType)>,
}

/// Build a map from struct name to its field info.
fn build_struct_map(
    struct_types: &[(&str, &Term<'_>)],
    union_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> Result<HashMap<String, StructInfo>, String> {
    let mut map = HashMap::new();
    for (name, sdef) in struct_types {
        if let Term::StructDef(_, fields) = sdef {
            let fs: Vec<(String, CType)> = fields
                .iter()
                .map(|(fnm, fc)| {
                    constraint_to_ctype(fc, union_names, struct_names)
                        .map(|ct| (fnm.to_string(), ct))
                })
                .collect::<Result<Vec<_>, _>>()?;
            map.insert(name.to_string(), StructInfo { fields: fs });
        }
    }
    Ok(map)
}

/// Build a map from union name to its variant info.
fn build_union_map(
    union_types: &[(&str, &Term<'_>)],
    union_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> Result<HashMap<String, UnionInfo>, String> {
    let mut map = HashMap::new();
    for (name, udef) in union_types {
        if let Term::UnionDef(_, variants) = udef {
            let mut vis = Vec::new();
            for (vname, fields) in variants.iter() {
                let fs: Vec<(String, CType)> = fields
                    .iter()
                    .map(|(fnm, fc)| {
                        constraint_to_ctype(fc, union_names, struct_names)
                            .map(|ct| (fnm.to_string(), ct))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                vis.push(VariantInfo {
                    name: vname.to_string(),
                    fields: fs,
                });
            }
            map.insert(name.to_string(), UnionInfo { variants: vis });
        }
    }
    Ok(map)
}

/// Extract type dependencies from a type definition (struct or union).
/// Returns the set of user-defined type names referenced by value.
fn type_dependencies(
    def: &Term<'_>,
    union_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> HashSet<String> {
    let mut deps = HashSet::new();
    let fields: Option<&[(crate::core::syntax::Name<'_>, &Term<'_>)]> = match def {
        Term::StructDef(_, f) => Some(*f),
        Term::UnionDef(_, variants) => {
            // Collect all payload fields from all variants
            let all: Vec<_> = variants
                .iter()
                .flat_map(|(_, fields)| fields.iter().map(|(n, t)| (*n, *t)))
                .collect();
            if all.is_empty() {
                return deps;
            }
            // Can't easily return a slice, just iterate
            for (_name, fty) in &all {
                collect_type_refs(fty, union_names, struct_names, &mut deps);
            }
            return deps;
        }
        _ => return deps,
    };
    if let Some(fs) = fields {
        for (_name, fty) in fs {
            collect_type_refs(fty, union_names, struct_names, &mut deps);
        }
    }
    deps
}

/// Recursively collect user-defined type names from a constraint term.
fn collect_type_refs(
    t: &Term<'_>,
    union_names: &HashSet<String>,
    struct_names: &HashSet<String>,
    deps: &mut HashSet<String>,
) {
    match t {
        Term::Builtin(name) | Term::Named(name) => {
            let s = name.to_string();
            if union_names.contains(&s) || struct_names.contains(&s) {
                deps.insert(s);
            }
        }
        Term::Pi(_, a, b) => {
            collect_type_refs(a, union_names, struct_names, deps);
            collect_type_refs(b, union_names, struct_names, deps);
        }
        Term::App(f, a) => {
            collect_type_refs(f, union_names, struct_names, deps);
            collect_type_refs(a, union_names, struct_names, deps);
        }
        _ => {}
    }
}

/// Emit a struct typedef using pointers for union-typed fields (for cyclic deps).
fn emit_struct_typedef_ptr(
    name: &str,
    sdef: &Term<'_>,
    union_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> Result<String, String> {
    let Term::StructDef(_, fields) = sdef else {
        return Ok(String::new());
    };
    let mut out = format!("// struct {name} (ptr cycle)\n");
    out.push_str(&format!("typedef struct {name} {{\n"));
    for (fname, fty) in fields.iter() {
        let cty = constraint_to_ctype(fty, union_names, struct_names)?;
        if matches!(cty, CType::Union(_)) {
            out.push_str(&format!("    {}* {};\n", cty.c_name(), fname));
        } else {
            out.push_str(&format!("    {} {};\n", cty.c_name(), fname));
        }
    }
    out.push_str(&format!("}} {name};\n"));
    Ok(out)
}

/// Emit a complete C source file from a list of top-level items.
///
/// On-demand codegen: only functions actually called from `#show` / `#expr`
/// are emitted.  Type parameters are erased at emission time.
pub fn emit_c(
    tops: &[TopLevel<'_>],
    raw_defs: &[TopLevel<'_>],
    fun_sigs: &[(&str, FunSig)],
    union_types: &[(&str, &Term<'_>)],
    struct_types: &[(&str, &Term<'_>)],
) -> Result<String, String> {
    let mut out = String::from("#include <stdio.h>\n#include <stdint.h>\n#include <stddef.h>\n\n");

    // Build separate name sets for struct and union resolution
    let union_names: HashSet<String> = union_types.iter().map(|(n, _)| n.to_string()).collect();
    let struct_names: HashSet<String> = struct_types.iter().map(|(n, _)| n.to_string()).collect();

    // Emit forward declarations for all types first
    for (name, _sdef) in struct_types {
        out.push_str(&format!("typedef struct {name} {name};\n"));
    }
    for (name, _udef) in union_types {
        out.push_str(&format!("typedef struct {name} {name};\n"));
    }
    out.push('\n');

    // Topological sort: emit types in dependency order.
    // A union variant payload may reference a struct by value → struct first.
    // A struct field may reference a union by value → union first.
    // For mutual cycles, we fall back to pointers in struct→union direction.
    let mut emitted: HashSet<String> = HashSet::new();
    let mut remaining: Vec<(&str, &Term<'_>, bool)> = Vec::new(); // (name, def, is_struct)
    for (n, s) in struct_types {
        remaining.push((n, *s, true));
    }
    for (n, u) in union_types {
        remaining.push((n, *u, false));
    }

    // Simple fixpoint: keep trying until all emitted or stuck
    let mut changed = true;
    while changed && !remaining.is_empty() {
        changed = false;
        let mut next: Vec<(&str, &Term<'_>, bool)> = Vec::new();
        for (name, def, is_struct) in remaining.drain(..) {
            let deps = type_dependencies(def, &union_names, &struct_names);
            let all_deps_emitted = deps.iter().all(|d| emitted.contains(d.as_str()));
            if all_deps_emitted || deps.is_empty() {
                if is_struct {
                    out.push_str(&emit_struct_typedef(
                        name,
                        def,
                        &union_names,
                        &struct_names,
                    )?);
                } else {
                    out.push_str(&emit_union_typedef(name, def, &union_names, &struct_names)?);
                }
                out.push('\n');
                emitted.insert(name.to_string());
                changed = true;
            } else {
                next.push((name, def, is_struct));
            }
        }
        remaining = next;
    }

    // Emit any remaining types (cycles) — struct fields with union deps use pointers
    if !remaining.is_empty() {
        for (name, def, is_struct) in remaining {
            if is_struct {
                out.push_str(&emit_struct_typedef_ptr(
                    name,
                    def,
                    &union_names,
                    &struct_names,
                )?);
            } else {
                out.push_str(&emit_union_typedef(name, def, &union_names, &struct_names)?);
            }
            out.push('\n');
        }
    }

    let union_map = build_union_map(union_types, &union_names, &struct_names)?;
    let struct_map = build_struct_map(struct_types, &union_names, &struct_names)?;

    // Collect output expressions (TLShow / TLExpr).
    let mut outputs: Vec<&Term<'_>> = Vec::new();
    for top in tops {
        match top {
            TopLevel::TLShow(term, _) | TopLevel::TLExpr(term, _) => outputs.push(term),
            _ => {}
        }
    }

    // Emit constants (zero-param, zero-lambda definitions) unconditionally.
    // These have no type params to erase and are pure data.
    for top in tops {
        if let TopLevel::TLDef(name, params, m_ret, body, _) = top
            && params.is_empty()
            && count_lams(body) == 0
        {
            out.push_str(&emit_def(
                name,
                params,
                *m_ret,
                body,
                fun_sigs,
                &union_map,
                &struct_map,
            )?);
            out.push('\n');
        }
    }

    // On-demand codegen for functions: walk output expressions to find called
    // function names, then emit only those definitions from raw_defs.
    // When there are no outputs (library mode), emit ALL functions.
    // Type params are erased at emission time via emit_def.
    // Constants are skipped here — already emitted unconditionally above.
    let called_names: HashSet<String> = if outputs.is_empty() {
        // Library mode: emit all function definitions.
        raw_defs
            .iter()
            .filter_map(|top| {
                if let TopLevel::TLDef(name, _, _, _, _) = top {
                    Some(name.to_string())
                } else {
                    None
                }
            })
            .collect()
    } else {
        // On-demand mode: only emit functions called from output expressions.
        collect_called_names(&outputs, raw_defs)
    };
    for raw_def in raw_defs {
        if let TopLevel::TLDef(name, params, m_ret, body, _) = raw_def {
            // Skip constants — already emitted unconditionally above.
            if params.is_empty() && count_lams(body) == 0 {
                continue;
            }
            if called_names.contains(*name) {
                out.push_str(&emit_def(
                    name,
                    params,
                    *m_ret,
                    body,
                    fun_sigs,
                    &union_map,
                    &struct_map,
                )?);
                out.push('\n');
            }
        }
    }

    if !outputs.is_empty() {
        out.push_str("int main(void) {\n");
        let mut match_counter: u32 = 0;
        for term in &outputs {
            let (expr, ctype) = emit_expr(
                term,
                &[],
                &mut Vec::new(),
                None,
                fun_sigs,
                &union_map,
                &struct_map,
            )?;
            // Handle match sentinels at top level (not inside a function)
            if expr.starts_with("match__") {
                let block = emit_match_block(&expr, &ctype, match_counter, &union_map);
                match_counter += 1;
                out.push_str(&block);
                // Print the result
                let r_var = format!("_r{}", match_counter - 1);
                match ctype {
                    CType::Str => out.push_str(&format!("    printf(\"%s\\n\", {});\n", r_var)),
                    CType::Int64 => {
                        out.push_str(&format!("    printf(\"%ld\\n\", (int64_t){});\n", r_var))
                    }
                    CType::Union(_) => {
                        out.push_str(&format!("    printf(\"%d\\n\", {}.tag);\n", r_var))
                    }
                    CType::Struct(_) => out.push_str("    printf(\"<struct>\\n\");\n"),
                }
            } else {
                match ctype {
                    CType::Str => {
                        out.push_str(&format!("    printf(\"%s\\n\", {});\n", expr));
                    }
                    CType::Int64 => {
                        out.push_str(&format!("    printf(\"%ld\\n\", (int64_t)({}));\n", expr));
                    }
                    CType::Union(_) => {
                        out.push_str(&format!("    printf(\"%d\\n\", ({}).tag);\n", expr));
                    }
                    CType::Struct(_) => {
                        out.push_str("    printf(\"<struct>\\n\");\n");
                    }
                }
            }
        }
        out.push_str("    return 0;\n}\n");
    } else {
        // Library-only: emit an empty main so it compiles to a runnable binary
        out.push_str("int main(void) {\n    return 0;\n}\n");
    }
    Ok(out)
}

/// Emit a C typedef for a union type (tagged union).
fn emit_union_typedef(
    name: &str,
    udef: &Term<'_>,
    union_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> Result<String, String> {
    let Term::UnionDef(_, variants) = udef else {
        return Ok(String::new());
    };
    let mut out = format!("// {name}\n");
    out.push_str(&format!("typedef struct {name} {{\n"));
    out.push_str("    int tag;\n");
    out.push_str("    union {\n");
    for (vname, fields) in variants.iter() {
        if fields.is_empty() {
            out.push_str(&format!("        struct {{ char _empty; }} {vname};\n"));
        } else {
            out.push_str("        struct { ");
            for (fname, fty) in fields.iter() {
                // Recursive reference if: Builtin(name)
                let is_self_ref = matches!(fty, Term::Builtin(tn) | Term::Named(tn) if *tn == name);
                if is_self_ref {
                    out.push_str(&format!("struct {}* {}; ", name, fname));
                } else {
                    let cty = constraint_to_ctype(fty, union_names, struct_names)?;
                    out.push_str(&format!("{} {}; ", cty.c_name(), fname));
                }
            }
            out.push_str(&format!("}} {vname};\n"));
        }
    }
    out.push_str("    } data;\n");
    out.push_str(&format!("}} {name};\n"));
    Ok(out)
}

/// Emit a C typedef for a struct type (product type with named fields).
fn emit_struct_typedef(
    name: &str,
    sdef: &Term<'_>,
    union_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> Result<String, String> {
    let Term::StructDef(_, fields) = sdef else {
        return Ok(String::new());
    };
    let mut out = format!("// struct {name}\n");
    out.push_str(&format!("typedef struct {name} {{\n"));
    for (fname, fty) in fields.iter() {
        let cty = constraint_to_ctype(fty, union_names, struct_names)?;
        out.push_str(&format!("    {} {};\n", cty.c_name(), fname));
    }
    out.push_str(&format!("}} {name};\n"));
    Ok(out)
}

/// Walk a set of Term trees and collect the names of all user-defined
/// functions that are called (including transitive dependencies).
/// Only returns names that appear in `raw_defs`.
fn collect_called_names<'bump>(
    outputs: &[&'bump Term<'bump>],
    raw_defs: &[TopLevel<'bump>],
) -> HashSet<String> {
    let def_names: HashSet<&str> = raw_defs
        .iter()
        .filter_map(|top| {
            if let TopLevel::TLDef(name, _, _, _, _) = top {
                Some(*name)
            } else {
                None
            }
        })
        .collect();
    let mut called = HashSet::new();
    // Seed with names found in output expressions.
    for term in outputs {
        collect_names_in_term(term, &def_names, &mut called);
    }
    // Transitive closure: also walk bodies of already-called functions
    // to discover indirect dependencies.
    let mut changed = true;
    while changed {
        changed = false;
        let prev_len = called.len();
        for raw_def in raw_defs {
            if let TopLevel::TLDef(name, _, _, body, _) = raw_def
                && called.contains(*name)
            {
                collect_names_in_term(body, &def_names, &mut called);
            }
        }
        if called.len() > prev_len {
            changed = true;
        }
    }
    called
}

/// Recursively walk a term looking for `Builtin(name)` / `Named(name)`
/// nodes that match known function definitions.
fn collect_names_in_term(term: &Term<'_>, def_names: &HashSet<&str>, called: &mut HashSet<String>) {
    match term {
        Term::Builtin(name) | Term::Named(name) => {
            if def_names.contains(name) {
                called.insert(name.to_string());
            }
        }
        Term::App(f, a) => {
            collect_names_in_term(f, def_names, called);
            collect_names_in_term(a, def_names, called);
        }
        Term::Lam(body) | Term::NamedLam(_, body) => {
            collect_names_in_term(body, def_names, called);
        }
        Term::Pi(_, a, b) => {
            collect_names_in_term(a, def_names, called);
            collect_names_in_term(b, def_names, called);
        }
        Term::Let(_, val, body, mconstr) => {
            collect_names_in_term(val, def_names, called);
            collect_names_in_term(body, def_names, called);
            if let Some(c) = mconstr {
                collect_names_in_term(c, def_names, called);
            }
        }
        Term::Annot(t, c) => {
            collect_names_in_term(t, def_names, called);
            collect_names_in_term(c, def_names, called);
        }
        Term::IfThenElse(c, t, f) => {
            collect_names_in_term(c, def_names, called);
            collect_names_in_term(t, def_names, called);
            collect_names_in_term(f, def_names, called);
        }
        Term::Match(scrut, branches) => {
            collect_names_in_term(scrut, def_names, called);
            for (_, binds, body) in *branches {
                for (_, bt) in *binds {
                    collect_names_in_term(bt, def_names, called);
                }
                collect_names_in_term(body, def_names, called);
            }
        }
        Term::StructCons(_, field_values) => {
            for v in *field_values {
                collect_names_in_term(v, def_names, called);
            }
        }
        Term::StructProj(subj, _) => {
            collect_names_in_term(subj, def_names, called);
        }
        Term::Variant(_, _, payloads) => {
            for p in *payloads {
                collect_names_in_term(p, def_names, called);
            }
        }
        Term::Refine(_, p, pred) => {
            collect_names_in_term(p, def_names, called);
            collect_names_in_term(pred, def_names, called);
        }
        Term::ByProof(subj_opt, tactics) => {
            if let Some(s) = subj_opt {
                collect_names_in_term(s, def_names, called);
            }
            for tac in *tactics {
                match tac {
                    crate::core::syntax::Tactic::Exact(t)
                    | crate::core::syntax::Tactic::Apply(t) => {
                        collect_names_in_term(t, def_names, called);
                    }
                    crate::core::syntax::Tactic::Have(_, t) => {
                        collect_names_in_term(t, def_names, called);
                    }
                    _ => {}
                }
            }
        }
        // Leaf nodes: no children to recurse into.
        Term::Var(_)
        | Term::LitInt(_)
        | Term::LitBool(_)
        | Term::LitStr(_)
        | Term::PrimOp(_)
        | Term::Universe(_)
        | Term::AutoProof
        | Term::RefParam
        | Term::UnionDef(..)
        | Term::StructDef(..) => {}
    }
}

/// Emit a top-level definition as a C function or constant.
fn emit_def(
    name: &str,
    params: &[(Name<'_>, Option<&Term<'_>>)],
    _m_ret: Option<&Term<'_>>,
    body: &Term<'_>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
    struct_map: &HashMap<String, StructInfo>,
) -> Result<String, String> {
    if params.is_empty() {
        let arity = count_lams(body);
        if arity == 0 {
            let (code, ctype) = emit_expr(
                body,
                &[],
                &mut Vec::new(),
                None,
                fun_sigs,
                union_map,
                struct_map,
            )?;
            Ok(format!(
                "const {} {} = {};\n",
                ctype.c_name(),
                escape_c_name(name),
                code
            ))
        } else {
            let pns: Vec<String> = (0..arity).map(|i| format!("arg_{}", i)).collect();
            let peeled = peel_lams(body, arity);
            let param_types = vec![CType::Int64; arity];
            emit_fun(
                name,
                &pns,
                &param_types,
                peeled,
                fun_sigs,
                union_map,
                struct_map,
            )
        }
    } else {
        // Filter out type-level (generic) params to match FunSig.
        let data_params: Vec<_> = params
            .iter()
            .filter(|(_, mc)| !mc.is_some_and(|c| is_type_universe(c)))
            .collect();
        let pns: Vec<String> = data_params.iter().map(|(n, _)| n.to_string()).collect();
        let param_types: Vec<CType> = fun_sigs
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, sig)| sig.param_types.clone())
            .unwrap_or_else(|| vec![CType::Int64; data_params.len()]);
        // Peel all lambdas (type params + data params).
        let peeled = peel_lams(body, params.len());
        emit_fun(
            name,
            &pns,
            &param_types,
            peeled,
            fun_sigs,
            union_map,
            struct_map,
        )
    }
}

/// Emit a C function with named parameters and a Term body.
///
/// `params` are the parameter names; `param_types` are the corresponding C types.
/// De Bruijn index 0 = rightmost (last) parameter.
fn emit_fun(
    name: &str,
    params: &[String],
    param_types: &[CType],
    body: &Term<'_>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
    struct_map: &HashMap<String, StructInfo>,
) -> Result<String, String> {
    let cps: Vec<String> = params
        .iter()
        .zip(param_types.iter())
        .map(|(p, ty)| format!("{} {}", ty.c_name(), escape_c_name(p)))
        .collect();
    let bd: Vec<String> = params.iter().rev().map(|p| escape_c_name(p)).collect();
    let mut var_types: Vec<CType> = param_types.iter().rev().cloned().collect();
    let (body_code, ret_ty) = emit_expr(
        body,
        &bd,
        &mut var_types,
        Some(name),
        fun_sigs,
        union_map,
        struct_map,
    )?;
    // If the body is a match, wrap it as a proper C block instead of
    // GCC statement expression.
    let return_stmt = if body_code.starts_with("match__") {
        // body_code is: "match__<scrut>__<ret_ty>__case0code__case1code__..."
        // Parse it out and emit as a switch block.
        let block = emit_match_block(&body_code, &ret_ty, 0, union_map);
        format!("{block}    return _r0;\n")
    } else {
        format!("    return {};\n", body_code)
    };
    Ok(format!(
        "{} {}({}) {{\n{}}}\n",
        ret_ty.c_name(),
        escape_c_name(name),
        cps.join(", "),
        return_stmt
    ))
}

/// Emit a match as a standard C switch block (not GCC expression).
/// Uses `union_map` to emit declarations for bound variables.
fn emit_match_block(
    code: &str,
    ret_ty: &CType,
    counter: u32,
    union_map: &HashMap<String, UnionInfo>,
) -> String {
    // Format: match__<scrut_type>__<scrut>__<ret_ty>__<idx>__<body>__...
    let parts: Vec<&str> = code.split("__").collect();
    if parts.len() < 5 {
        return "    return 0;\n".to_string();
    }
    let scrut_ty = parts[1];
    let scrut = parts[2];
    let ret_name = ret_ty.c_name();
    let s_var = format!("_s{}", counter);
    let r_var = format!("_r{}", counter);
    let mut out = String::new();
    out.push_str(&format!("    {scrut_ty} {s_var} = {scrut};\n"));
    out.push_str(&format!("    {ret_name} {r_var};\n"));
    out.push_str(&format!("    switch ({s_var}.tag) {{\n"));
    let mut i: usize = 4;
    while i + 1 < parts.len() {
        let case_idx: usize = parts[i].parse().unwrap_or(0);
        i += 1;
        // Decode bind count
        let bind_count: usize = parts[i].parse().unwrap_or(0);
        i += 1;
        // Decode bind names and types
        let mut bind_names: Vec<String> = Vec::new();
        let mut bind_types: Vec<String> = Vec::new();
        for _ in 0..bind_count {
            if i < parts.len() {
                bind_names.push(parts[i].to_string());
                i += 1;
            }
            if i < parts.len() {
                bind_types.push(parts[i].to_string());
                i += 1;
            }
        }
        // Build bind declarations: initialize from scrutinee fields
        // Skip wildcard binds (named "_" or empty).
        let bind_decls = if bind_count > 0 {
            if let Some(info) = union_map.get(scrut_ty) {
                if let Some(vi) = info.variants.get(case_idx) {
                    bind_names
                        .iter()
                        .zip(bind_types.iter())
                        .enumerate()
                        .filter(|(_, (bname, _))| !bname.is_empty() && bname.as_str() != "_")
                        .map(|(j, (bname, bty))| {
                            let field_name = vi
                                .fields
                                .get(j)
                                .map(|(fnm, _)| fnm.as_str())
                                .unwrap_or(bname.as_str());
                            format!("{bty} {bname} = {s_var}.data.{}.{field_name}; ", vi.name)
                        })
                        .collect::<Vec<_>>()
                        .join("")
                } else {
                    String::new()
                }
            } else {
                String::new()
            }
        } else {
            String::new()
        };
        // Body code
        let case_code = if i < parts.len() {
            parts[i].replace('\x1e', ", ")
        } else {
            String::from("0")
        };
        i += 1;
        out.push_str(&format!(
            "    case {}: {{ {bind_decls}{r_var} = {}; }} break;\n",
            case_idx, case_code
        ));
    }
    out.push_str(&format!("    default: {r_var} = 0; break;\n"));
    out.push_str("    }\n");
    out
}

fn count_lams(term: &Term<'_>) -> usize {
    match term {
        Term::Lam(body) => 1 + count_lams(body),
        Term::Annot(inner, _) => count_lams(inner),
        _ => 0,
    }
}

fn peel_lams<'a>(term: &'a Term<'a>, n: usize) -> &'a Term<'a> {
    let mut t = term;
    let mut remaining = n;
    while remaining > 0 {
        match t {
            Term::Lam(body) => {
                t = body;
                remaining -= 1;
            }
            Term::Annot(inner, _) => {
                t = inner;
            }
            _ => break,
        }
    }
    t
}

/// Emit a Term as a C expression, returning the emitted code and its C type.
///
/// `bound` holds the C variable names in De Bruijn order (index 0 = most
/// recently bound).  `var_types` holds the C types in the same De Bruijn
/// order — the two stacks are kept in sync by push/pop at binder sites.
/// `self_name` is `Some(name)` inside a recursive function body.
fn emit_expr(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
    struct_map: &HashMap<String, StructInfo>,
) -> Result<(String, CType), String> {
    match term {
        Term::LitInt(n) => Ok((n.to_string(), CType::Int64)),
        Term::LitBool(b) => Ok((if *b { "1" } else { "0" }.into(), CType::Int64)),
        Term::LitStr(s) => Ok((format!("\"{}\"", s), CType::Str)),

        Term::Var(i) => {
            let ty = var_types.get(*i).cloned().unwrap_or(CType::Int64);
            /*if bound.len() <= *i {
                println!("{:?} {:?}", bound, var_types);
            }*/
            Ok((bound[*i].clone(), ty))
        }

        Term::Let(name, val, body, _) => {
            let (v, val_ty) = emit_expr(
                val, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            let ty_name = val_ty.c_name();
            var_types.insert(0, val_ty);
            let mut ext: Vec<String> = vec![(*name).to_string()];
            ext.extend_from_slice(bound);
            let (b, body_ty) = emit_expr(
                body, &ext, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            var_types.remove(0);
            Ok((
                format!("({{ {} {} = {}; {}; }})", ty_name, name, v, b),
                body_ty,
            ))
        }

        Term::Lam(body) => {
            var_types.insert(0, CType::Int64);
            let (b, ret_ty) = emit_expr(
                body, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            var_types.remove(0);
            // Lambda wrapping is done by emit_fun via emit_def.
            // We return the body code + return type for inference.
            Ok((b, ret_ty))
        }

        Term::IfThenElse(c, t, f) => {
            let (cc, _) = emit_expr(
                c, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            let (ct, t_ty) = emit_expr(
                t, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            let (cf, _) = emit_expr(
                f, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            Ok((format!("({}) ? ({}) : ({})", cc, ct, cf), t_ty))
        }

        // Function calls: look up the called function's return type.
        Term::App(_, _) => emit_app(
            term, bound, var_types, self_name, fun_sigs, union_map, struct_map,
        ),

        Term::Annot(inner, _) => emit_expr(
            inner, bound, var_types, self_name, fun_sigs, union_map, struct_map,
        ),
        Term::Builtin(name) | Term::Named(name) => {
            let ty = fun_sigs
                .iter()
                .find(|(n, _)| *n == *name)
                .map(|(_, sig)| sig.ret_type.clone())
                .unwrap_or(CType::Int64);
            Ok((escape_c_name(name), ty))
        }
        Term::UnionDef(..) => Ok((String::new(), CType::Int64)),
        Term::StructDef(..) => Ok((String::new(), CType::Int64)),
        Term::StructCons(sname, field_values) => {
            let type_name: String = sname.to_string();
            let field_codes: Vec<String> = field_values
                .iter()
                .map(|v| {
                    let (code, _) = emit_expr(
                        v, bound, var_types, self_name, fun_sigs, union_map, struct_map,
                    )?;
                    Ok(code)
                })
                .collect::<Result<Vec<_>, String>>()?;
            Ok((
                format!("(({}){{ {} }})", type_name, field_codes.join(", ")),
                CType::Struct(type_name),
            ))
        }
        Term::StructProj(subject, idx) => {
            let (scode, sty) = emit_expr(
                subject, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            // Look up the struct type to get the real field name and type
            if let CType::Struct(ref sname) = sty
                && let Some(info) = struct_map.get(sname)
                && let Some((fname, ftype)) = info.fields.get(*idx)
            {
                return Ok((format!("({}).{}", scode, fname), ftype.clone()));
            }
            // Fallback: use index-based access
            Ok((format!("({})._f{}", scode, idx), CType::Int64))
        }
        Term::Variant(uname, idx, payloads) => {
            let type_name: String = uname.to_string();
            // Look up variant info for field names
            let data_init = if let Some(info) = union_map.get(&type_name) {
                if let Some(vi) = info.variants.get(*idx) {
                    if vi.fields.is_empty() {
                        format!("{{ .{} = {{0}} }}", vi.name)
                    } else {
                        let field_inits: Vec<String> = vi
                            .fields
                            .iter()
                            .zip(payloads.iter())
                            .map(|((fnm, fty), p)| {
                                let (code, pty) = emit_expr(
                                    p, bound, var_types, self_name, fun_sigs, union_map, struct_map,
                                )?;
                                // Recursive field? Check field type AND payload type.
                                let is_rec = if let CType::Union(un) = fty {
                                    un == &type_name
                                } else if let CType::Union(ref un) = pty {
                                    un == &type_name
                                } else {
                                    false
                                };
                                Ok(if is_rec {
                                    format!(".{} = &{}", fnm, code)
                                } else {
                                    format!(".{} = {}", fnm, code)
                                })
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        format!("{{ .{} = {{ {} }} }}", vi.name, field_inits.join(", "))
                    }
                } else {
                    String::from("{0}")
                }
            } else {
                String::from("{0}")
            };
            Ok((
                format!(
                    "(({}){{ .tag = {}, .data = {} }})",
                    type_name, idx, data_init
                ),
                CType::Union(type_name),
            ))
        }
        Term::Match(_scrut, branches) => {
            // Emit as "match__<sc_ty>__<sc>__<ret_ty>__<idx>__<n>__<name>__<type>__...__<body>__..."
            let (sc, sc_ty) = emit_expr(
                _scrut, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            let mut parts = vec!["match".to_string(), sc_ty.c_name(), sc];
            let mut ret_ty = CType::Int64;
            for (idx, binds, body) in branches.iter() {
                let mut ext = bound.to_vec();
                let mut ext_types = var_types.clone();
                for (name, _) in binds.iter().rev() {
                    ext.insert(0, (*name).to_string());
                    ext_types.insert(0, CType::Int64);
                }
                let (bc, bty) = emit_expr(
                    body,
                    &ext,
                    &mut ext_types,
                    self_name,
                    fun_sigs,
                    union_map,
                    struct_map,
                )?;
                ret_ty = bty;
                let escaped = bc.replace(',', "\x1e");
                parts.push(idx.to_string());
                // Encode bind info: count + name/type pairs
                parts.push(binds.len().to_string());
                for (name, ty) in binds.iter() {
                    parts.push((*name).to_string());
                    // Look up the C type using both union and struct name sets
                    let un: HashSet<String> = union_map.keys().cloned().collect();
                    let sn: HashSet<String> = struct_map.keys().cloned().collect();
                    parts.push(constraint_to_ctype(ty, &un, &sn)?.c_name());
                }
                parts.push(escaped);
            }
            let ty_str = ret_ty.c_name();
            parts.insert(3, ty_str);
            Ok((parts.join("__"), ret_ty))
        }
        _ => Err(format!("emit_expr: unrecognized term {:?}", term)),
    }
}

fn emit_app(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
    struct_map: &HashMap<String, StructInfo>,
) -> Result<(String, CType), String> {
    let Term::App(f, a) = term else {
        unreachable!()
    };
    // Binary operators: (prim left) right  →  PrimOp applied to two args.
    if let Term::App(prim, left) = *f
        && let Term::PrimOp(op) = *prim
    {
        let (ls, _) = emit_expr(
            left, bound, var_types, self_name, fun_sigs, union_map, struct_map,
        )?;
        let (rs, _) = emit_expr(
            a, bound, var_types, self_name, fun_sigs, union_map, struct_map,
        )?;
        return Ok((emit_binop(*op, &ls, &rs), CType::Int64));
    }
    // Unary / partial application: just emit the argument.
    if matches!(*f, Term::PrimOp(_)) {
        let (as_, ty) = emit_expr(
            a, bound, var_types, self_name, fun_sigs, union_map, struct_map,
        )?;
        return Ok((as_, ty));
    }
    // Function call.
    let (func, args) = collect_call_args(
        term, bound, var_types, self_name, fun_sigs, union_map, struct_map,
    )?;
    let param_count = fun_sigs
        .iter()
        .find(|(n, _)| *n == func)
        .map(|(_, sig)| sig.param_types.len())
        .unwrap_or(0);
    // Strip excess arguments (type-level args come first, before data args).
    // Keep only the last `param_count` arguments.
    let trimmed: Vec<String> = if args.len() > param_count {
        args[args.len() - param_count..].to_vec()
    } else {
        args
    };
    let ret_ty = fun_sigs
        .iter()
        .find(|(n, _)| *n == func)
        .map(|(_, sig)| sig.ret_type.clone())
        .unwrap_or(CType::Int64);
    Ok((format!("{}({})", func, trimmed.join(", ")), ret_ty))
}

fn collect_call_args(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
    struct_map: &HashMap<String, StructInfo>,
) -> Result<(String, Vec<String>), String> {
    match term {
        Term::App(f, a) => {
            let (func, mut args) = collect_call_args(
                f, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            let (as_, _) = emit_expr(
                a, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            args.push(as_);
            Ok((func, args))
        }
        _ => {
            let (s, _) = emit_expr(
                term, bound, var_types, self_name, fun_sigs, union_map, struct_map,
            )?;
            Ok((s, Vec::new()))
        }
    }
}

fn emit_binop(op: PrimOp, left: &str, right: &str) -> String {
    match op {
        PrimOp::Add => format!("({left} + {right})"),
        PrimOp::Sub => format!("({left} - {right})"),
        PrimOp::Mul => format!("({left} * {right})"),
        PrimOp::Div => format!("({left} / {right})"),
        PrimOp::Mod_ => format!("({left} % {right})"),
        PrimOp::Eq => format!("({left} == {right})"),
        PrimOp::Neq => format!("({left} != {right})"),
        PrimOp::Lt => format!("({left} < {right})"),
        PrimOp::Gt => format!("({left} > {right})"),
        PrimOp::Le => format!("({left} <= {right})"),
        PrimOp::Ge => format!("({left} >= {right})"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::ir::FunSig;
    use crate::core::pool::TermArena;
    use crate::core::syntax::{Name, PrimOp};
    use bumpalo::Bump;

    fn setup() -> (&'static Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        (b, TermArena::new(b))
    }

    fn sig(name: &str, param_types: Vec<CType>, ret_type: CType) -> (&str, FunSig) {
        let leaked: &'static str = Box::leak(name.to_string().into_boxed_str());
        (
            leaked,
            FunSig {
                param_types,
                ret_type,
            },
        )
    }

    fn emit(tops: &[TopLevel<'_>], fun_sigs: &[(&str, FunSig)]) -> String {
        emit_c(tops, tops, fun_sigs, &[], &[]).unwrap()
    }

    // ── Literals ──

    #[test]
    fn int_literal_uses_ld() {
        let (_b, arena) = setup();
        let c = emit(&[TopLevel::TLShow(arena.lit_int(42), 0..0)], &[]);
        assert!(c.contains("42"));
        assert!(c.contains("%ld"));
    }

    #[test]
    fn str_literal_uses_s() {
        let (_b, arena) = setup();
        let c = emit(
            &[TopLevel::TLShow(arena.lit_str(arena.alloc_str("hi")), 0..0)],
            &[],
        );
        assert!(c.contains("\"hi\""));
        assert!(c.contains("%s"));
    }

    #[test]
    fn bool_literal_emits_0_or_1() {
        let (_b, arena) = setup();
        let c = emit(&[TopLevel::TLShow(arena.lit_bool(true), 0..0)], &[]);
        assert!(c.contains("(int64_t)(1)"));
    }

    // ── Constants ──

    #[test]
    fn int_const_def() {
        let (_b, arena) = setup();
        let name = arena.alloc_str("x");
        let c = emit(
            &[TopLevel::TLDef(name, &[], None, arena.lit_int(5), 0..0)],
            &[],
        );
        assert!(c.contains("const int64_t x = 5;"));
    }

    #[test]
    fn str_const_def() {
        let (_b, arena) = setup();
        let name = arena.alloc_str("g");
        let c = emit(
            &[TopLevel::TLDef(
                name,
                &[],
                None,
                arena.lit_str(arena.alloc_str("hi")),
                0..0,
            )],
            &[],
        );
        assert!(c.contains("const char* g"));
        assert!(c.contains("\"hi\""));
    }

    // ── Functions (no FunSig, lam-tree) ──

    #[test]
    fn lam_function_defaults_to_int64_params_and_return() {
        let (_b, arena) = setup();
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(1)),
            arena.var(0),
        );
        let lam = arena.lam(arena.lam(body));
        let name = arena.alloc_str("add");
        let c = emit(&[TopLevel::TLDef(name, &[], None, lam, 0..0)], &[]);
        assert!(c.contains("int64_t add(int64_t arg_0, int64_t arg_1)"));
    }

    #[test]
    fn lam_returning_str_infers_str_return_type() {
        let (_b, arena) = setup();
        let lam = arena.lam(arena.lit_str(arena.alloc_str("hi")));
        let name = arena.alloc_str("greet");
        let c = emit(&[TopLevel::TLDef(name, &[], None, lam, 0..0)], &[]);
        assert!(c.contains("const char* greet(int64_t arg_0)"));
        assert!(c.contains("\"hi\""));
    }

    // ── Functions WITH FunSig ──

    #[test]
    fn func_with_str_param_uses_const_char_ptr() {
        let (_b, arena) = setup();
        let name = arena.alloc_str("echo");
        let params: &[(Name, Option<&Term>)] = arena.alloc_slice(&[(
            arena.alloc_str("s"),
            Some(arena.builtin(arena.alloc_str("str"))),
        )]);
        let desugared = arena.annot(
            arena.lam(arena.var(0)),
            arena.pi(
                arena.alloc_str("s"),
                arena.builtin(arena.alloc_str("str")),
                arena.builtin(arena.alloc_str("str")),
            ),
        );
        let sigs = &[sig("echo", vec![CType::Str], CType::Str)];
        let c = emit(
            &[TopLevel::TLDef(
                name,
                params,
                Some(arena.builtin(arena.alloc_str("str"))),
                desugared,
                0..0,
            )],
            sigs,
        );
        assert!(c.contains("const char* echo(const char* s)"));
    }

    #[test]
    fn func_with_mixed_params() {
        let (_b, arena) = setup();
        let name = arena.alloc_str("f");
        let params: &[(Name, Option<&Term>)] = arena.alloc_slice(&[
            (
                arena.alloc_str("a"),
                Some(arena.builtin(arena.alloc_str("int"))),
            ),
            (
                arena.alloc_str("b"),
                Some(arena.builtin(arena.alloc_str("str"))),
            ),
        ]);
        let desugared = arena.annot(
            arena.lam(arena.lam(arena.var(1))),
            arena.pi(
                arena.alloc_str("a"),
                arena.builtin(arena.alloc_str("int")),
                arena.pi(
                    arena.alloc_str("b"),
                    arena.builtin(arena.alloc_str("str")),
                    arena.builtin(arena.alloc_str("int")),
                ),
            ),
        );
        let sigs = &[sig("f", vec![CType::Int64, CType::Str], CType::Int64)];
        let c = emit(
            &[TopLevel::TLDef(
                name,
                params,
                Some(arena.builtin(arena.alloc_str("int"))),
                desugared,
                0..0,
            )],
            sigs,
        );
        assert!(c.contains("int64_t f(int64_t a, const char* b)"));
    }

    // ── Function calls ──

    #[test]
    fn call_to_function_uses_fun_sig_return_type() {
        let (_b, arena) = setup();
        let fn_name = arena.alloc_str("greet");
        let def = TopLevel::TLDef(
            fn_name,
            &[],
            Some(arena.builtin(arena.alloc_str("str"))),
            arena.annot(
                arena.lit_str(arena.alloc_str("hi")),
                arena.builtin(arena.alloc_str("str")),
            ),
            0..0,
        );
        let sig = FunSig {
            param_types: vec![],
            ret_type: CType::Str,
        };
        let show = TopLevel::TLShow(arena.builtin(fn_name), 0..0);
        let tops = &[def, show];
        let c = emit(tops, &[(fn_name, sig)]);
        assert!(c.contains("%s"));
        assert!(c.contains("const char* greet"));
    }

    #[test]
    fn emit_undefined_func_call_still_emits() {
        let (_b, arena) = setup();
        let n = arena.alloc_str("s");
        let call = arena.app(arena.builtin(n), arena.lit_str(arena.alloc_str("hi")));
        let tops = &[TopLevel::TLShow(call, 0..0)];
        let c = emit(tops, &[]);
        assert!(c.contains("s("));
    }

    #[test]
    fn emit_let_str_printf_format() {
        let (_b, arena) = setup();
        let term = arena.let_(
            arena.alloc_str("s"),
            arena.lit_str(arena.alloc_str("hi")),
            arena.var(0),
            None,
        );
        let c = emit(&[TopLevel::TLShow(term, 0..0)], &[]);
        assert!(c.contains("%s"));
        assert!(c.contains("const char* s"));
    }

    #[test]
    fn emit_multiple_defs_and_outputs() {
        let (_b, arena) = setup();
        let tops = &[
            TopLevel::TLDef(arena.alloc_str("a"), &[], None, arena.lit_int(1), 0..0),
            TopLevel::TLDef(
                arena.alloc_str("b"),
                &[],
                None,
                arena.lit_str(arena.alloc_str("two")),
                0..0,
            ),
            TopLevel::TLShow(arena.lit_int(3), 0..0),
            TopLevel::TLShow(arena.lit_str(arena.alloc_str("four")), 0..0),
        ];
        let c = emit(tops, &[]);
        assert!(c.contains("const int64_t a = 1;"));
        assert!(c.contains("const char* b = \"two\";"));
        assert!(c.contains("%ld"));
        assert!(c.contains("%s"));
    }

    // ── Union codegen ──

    /// Build a union typedef with empty and payload variants.
    #[test]
    fn union_typedef_with_recursive_field() {
        let (_b, arena) = setup();
        let nat_name = arena.alloc_str("Nat");
        let zero_variant: (Name, &[(Name, &Term)]) =
            (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
        let succ_fields: &[(Name, &Term)] =
            arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
        let succ_variant: (Name, &[(Name, &Term)]) = (arena.alloc_str("Succ"), succ_fields);
        let variants: &[(Name, &[(Name, &Term)])] =
            arena.alloc_slice(&[zero_variant, succ_variant]);
        let nat_udef = arena.union_def(nat_name, variants);
        let union_types: &[(&str, &Term)] = arena.bump().alloc([(nat_name, nat_udef)]);

        let top_name = arena.alloc_str("zero");
        let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
        let tops = &[TopLevel::TLDef(
            top_name,
            &[],
            Some(arena.builtin(nat_name)),
            zero_v,
            0..0,
        )];

        let c = emit_c(tops, &[], &[], union_types, &[]).unwrap();
        // Typedef uses struct pointer for recursive field
        assert!(
            c.contains("struct Nat* pred;"),
            "expected struct Nat* pred; in:\n{c}"
        );
        // Empty variant uses proper initializer
        assert!(c.contains(".Zero = {0}"), "expected .Zero = {{0}} in:\n{c}");
        // Constant declaration uses union type name
        assert!(
            c.contains("const Nat zero ="),
            "expected const Nat zero in:\n{c}"
        );
    }

    /// Recursive variant construction emits address-of.
    #[test]
    fn union_recursive_variant_emits_address_of() {
        let (_b, arena) = setup();
        let nat_name = arena.alloc_str("Nat");
        let zero_variant: (Name, &[(Name, &Term)]) =
            (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
        let succ_fields: &[(Name, &Term)] =
            arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
        let succ_variant: (Name, &[(Name, &Term)]) = (arena.alloc_str("Succ"), succ_fields);
        let variants: &[(Name, &[(Name, &Term)])] =
            arena.alloc_slice(&[zero_variant, succ_variant]);
        let nat_udef = arena.union_def(nat_name, variants);
        let union_types: &[(&str, &Term)] = arena.bump().alloc([(nat_name, nat_udef)]);

        // Build: Succ(Zero)
        let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
        let one_v = arena.variant(nat_name, 1, arena.alloc_slice(&[zero_v]));
        let tops = &[TopLevel::TLDef(
            arena.alloc_str("one"),
            &[],
            Some(arena.builtin(nat_name)),
            one_v,
            0..0,
        )];

        let c = emit_c(tops, &[], &[], union_types, &[]).unwrap();
        // Recursive reference must emit & (address-of) for the pointer field
        assert!(
            c.contains("&((Nat)"),
            "expected &((Nat){{...}}) for recursive field in:\n{c}"
        );
    }
}
