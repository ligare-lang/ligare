//! Match block emission for C code generation.
//!
//! `MatchEmitter` converts structured match plans into C `switch` blocks
//! with proper bind declarations.

use crate::backend::c::names::NameResolver;
use crate::backend::c::types::EnumInfo;
use crate::backend::c::value::{MatchBind, MatchPlan};
use crate::backend::ir::CType;
use std::collections::HashMap;

/// Emits match expressions as C `switch` blocks.
///
/// References the enum map (via `&HashMap`) for field-name resolution
/// when emitting bind declarations.
pub struct MatchEmitter {
    names: NameResolver,
}

impl MatchEmitter {
    /// Create a new match emitter.
    pub fn new() -> Self {
        Self {
            names: NameResolver::new(),
        }
    }

    /// Emit a match as a standard C switch block (not GCC expression).
    /// Uses `enum_map` to emit declarations for bound variables.
    pub fn emit(
        &self,
        plan: &MatchPlan,
        counter: u32,
        enum_map: &HashMap<String, EnumInfo>,
    ) -> String {
        let scrut_ty = plan.scrut_type.c_name();
        let ret_name = plan.ret_type.c_name();
        let s_var = self.names.scrut_temp(counter);
        let r_var = self.names.result_temp(counter);
        let mut out = String::new();
        out.push_str(&format!(
            "    {scrut_ty} {s_var} = {};\n",
            plan.scrut_code.as_str()
        ));
        out.push_str(&format!("    {ret_name} {r_var};\n"));
        out.push_str(&format!("    switch ({s_var}.tag) {{\n"));
        for case in &plan.cases {
            let bind_decls = self.build_bind_decls(
                &plan.scrut_type,
                case.variant_idx,
                &s_var,
                &case.binds,
                enum_map,
            );
            out.push_str(&format!(
                "    case {}: {{ {bind_decls}{r_var} = {}; }} break;\n",
                case.variant_idx,
                case.body_code.as_str()
            ));
        }
        out.push_str(&format!(
            "    default: {r_var} = {}; break;\n",
            plan.ret_type.c_default_value()
        ));
        out.push_str("    }\n");
        out
    }

    /// Emit a match as a GCC-style statement expression.
    pub fn emit_expr(
        &self,
        plan: &MatchPlan,
        counter: u32,
        enum_map: &HashMap<String, EnumInfo>,
    ) -> String {
        let block = self.emit(plan, counter, enum_map);
        let r_var = self.names.result_temp(counter);
        format!("({{\n{block}    {r_var};\n}})")
    }

    /// Build bind declarations for a match case, looking up field names
    /// from the enum info. Skips wildcard binds (named "_" or empty).
    fn build_bind_decls(
        &self,
        scrut_ty: &CType,
        case_idx: usize,
        s_var: &str,
        binds: &[MatchBind],
        enum_map: &HashMap<String, EnumInfo>,
    ) -> String {
        if binds.is_empty() {
            return String::new();
        }
        let CType::Enum(enum_name) = scrut_ty else {
            return String::new();
        };
        if let Some(info) = enum_map.get(enum_name)
            && let Some(vi) = info.variants.get(case_idx)
        {
            return binds
                .iter()
                .enumerate()
                .filter(|(_, bind)| !bind.name.is_empty() && bind.name.as_str() != "_")
                .map(|(j, bind)| {
                    let field_name = vi
                        .fields
                        .get(j)
                        .map(|field| field.name.as_str())
                        .unwrap_or(bind.name.as_str());
                    let access = format!("{s_var}.data.{}.{field_name}", vi.name);
                    let value = vi
                        .fields
                        .get(j)
                        .filter(|field| field.boxed)
                        .map(|_| format!("*({access})"))
                        .unwrap_or(access);
                    format!("{} {} = {value}; ", bind.ctype.c_name(), bind.name,)
                })
                .collect::<Vec<_>>()
                .join("");
        }
        String::new()
    }
}

impl Default for MatchEmitter {
    fn default() -> Self {
        Self::new()
    }
}
