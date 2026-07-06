use super::*;

impl CEmitter {
    pub(super) fn collect_extern_names(&self, raw_defs: &[TopLevel<'_>]) -> HashSet<String> {
        raw_defs
            .iter()
            .filter_map(|top| {
                if let TopLevel::TLExternDef(name, ..) = top {
                    Some((*name).to_string())
                } else {
                    None
                }
            })
            .collect()
    }

    pub(super) fn collect_called_extern_names(
        &self,
        tops: &[TopLevel<'_>],
        outputs: &[&Term<'_>],
        raw_defs: &[TopLevel<'_>],
        called_names: &HashSet<String>,
        extern_names: &HashSet<String>,
    ) -> HashSet<String> {
        let extern_name_refs = extern_names
            .iter()
            .map(String::as_str)
            .collect::<HashSet<_>>();
        let mut called = HashSet::new();
        if let Some(main_body) = self.runtime_main_body(tops) {
            self.name_resolver.collect_matching_names_in_term(
                main_body,
                &extern_name_refs,
                &mut called,
            );
        }
        for term in outputs {
            self.name_resolver
                .collect_matching_names_in_term(term, &extern_name_refs, &mut called);
        }
        for raw_def in raw_defs {
            if let TopLevel::TLDef(name, _, _, body, _) = raw_def
                && called_names.contains(*name)
            {
                self.name_resolver.collect_matching_names_in_term(
                    body,
                    &extern_name_refs,
                    &mut called,
                );
            }
        }
        called
    }

    pub(super) fn extern_clone_helpers_required(
        &self,
        called_extern_names: &HashSet<String>,
        clone_type_names: &HashSet<String>,
    ) -> bool {
        self.fun_sigs.iter().any(|(name, sig)| {
            called_extern_names.contains(name)
                && (sig
                    .param_types
                    .iter()
                    .any(|ty| self.ctype_requires_clone(ty, clone_type_names))
                    || self.ctype_requires_clone(&sig.ret_type, clone_type_names))
        })
    }

    fn ctype_requires_clone(&self, ctype: &CType, clone_type_names: &HashSet<String>) -> bool {
        match ctype {
            CType::Enum(name) | CType::Struct(name) => clone_type_names.contains(name),
            _ => false,
        }
    }

    pub(super) fn emit_clone_helpers(
        &self,
        out: &mut String,
        clone_type_names: &HashSet<String>,
        allocator: &GlobalAllocator,
    ) {
        let mut names = clone_type_names.iter().cloned().collect::<Vec<_>>();
        names.sort();
        for name in &names {
            if self.type_analyzer.struct_map().contains_key(name) {
                let ctype = CType::Struct(name.clone());
                out.push_str(&format!(
                    "static {} {}({} value);\n",
                    ctype.c_name(),
                    ExpressionEmitter::clone_helper_name(&ctype),
                    ctype.c_name()
                ));
            } else if self.type_analyzer.enum_map().contains_key(name) {
                let ctype = CType::Enum(name.clone());
                out.push_str(&format!(
                    "static {} {}({} value);\n",
                    ctype.c_name(),
                    ExpressionEmitter::clone_helper_name(&ctype),
                    ctype.c_name()
                ));
            }
        }
        if !names.is_empty() {
            out.push('\n');
        }
        for name in &names {
            if let Some(info) = self.type_analyzer.struct_map().get(name) {
                out.push_str(&self.emit_struct_clone_helper(
                    name,
                    info,
                    clone_type_names,
                    allocator,
                ));
            } else if let Some(info) = self.type_analyzer.enum_map().get(name) {
                out.push_str(&self.emit_enum_clone_helper(name, info, clone_type_names, allocator));
            }
            out.push('\n');
        }
    }

    fn emit_struct_clone_helper(
        &self,
        name: &str,
        info: &StructInfo,
        clone_type_names: &HashSet<String>,
        allocator: &GlobalAllocator,
    ) -> String {
        let ctype = CType::Struct(name.to_string());
        let ty = ctype.c_name();
        let helper = ExpressionEmitter::clone_helper_name(&ctype);
        let mut out = format!("static {ty} {helper}({ty} value) {{\n    {ty} out = value;\n");
        for (field_idx, field) in info.fields.iter().enumerate() {
            let access = format!("value.{}", field.name);
            let value_expr = self.clone_field_expr(
                &field.logical_type,
                field.boxed,
                &access,
                clone_type_names,
                allocator,
                &format!("{ty}_{field_idx}"),
            );
            if value_expr != access {
                out.push_str(&format!("    out.{} = {};\n", field.name, value_expr));
            }
        }
        out.push_str("    return out;\n}\n");
        out
    }

    fn emit_enum_clone_helper(
        &self,
        name: &str,
        info: &EnumInfo,
        clone_type_names: &HashSet<String>,
        allocator: &GlobalAllocator,
    ) -> String {
        let ctype = CType::Enum(name.to_string());
        let ty = ctype.c_name();
        let helper = ExpressionEmitter::clone_helper_name(&ctype);
        let mut out = format!("static {ty} {helper}({ty} value) {{\n    switch (value.tag) {{\n");
        for (variant_idx, variant) in info.variants.iter().enumerate() {
            if variant.fields.is_empty() {
                out.push_str(&format!("    case {variant_idx}: return value;\n"));
                continue;
            }
            let field_inits = variant
                .fields
                .iter()
                .enumerate()
                .map(|(field_idx, field)| {
                    let access = format!("value.data.{}.{}", variant.name, field.name);
                    let value_expr = self.clone_field_expr(
                        &field.logical_type,
                        field.boxed,
                        &access,
                        clone_type_names,
                        allocator,
                        &format!("{ty}_{variant_idx}_{field_idx}"),
                    );
                    format!(".{} = {}", field.name, value_expr)
                })
                .collect::<Vec<_>>()
                .join(", ");
            out.push_str(&format!(
                "    case {variant_idx}: return (({ty}){{ .tag = {variant_idx}, .data = {{ .{} = {{ {} }} }} }});\n",
                variant.name, field_inits
            ));
        }
        out.push_str("    default: return value;\n    }\n}\n");
        out
    }

    fn clone_field_expr(
        &self,
        logical_type: &CType,
        boxed: bool,
        access: &str,
        clone_type_names: &HashSet<String>,
        allocator: &GlobalAllocator,
        suffix: &str,
    ) -> String {
        if boxed {
            let pointee_ty = logical_type.c_name();
            let helper_value =
                self.clone_value_expr(logical_type, &format!("*({access})"), clone_type_names);
            let ptr_name = format!("_ligare_clone_box_{suffix}");
            return format!(
                "({{ {pointee_ty}* {ptr_name} = NULL; if ({access} != NULL) {{ {ptr_name} = ({pointee_ty}*){}(sizeof({pointee_ty})); *{ptr_name} = {}; }} {ptr_name}; }})",
                allocator.allocate, helper_value
            );
        }
        self.clone_value_expr(logical_type, access, clone_type_names)
    }

    fn clone_value_expr(
        &self,
        ctype: &CType,
        access: &str,
        clone_type_names: &HashSet<String>,
    ) -> String {
        if self.ctype_requires_clone(ctype, clone_type_names) {
            format!("{}({access})", ExpressionEmitter::clone_helper_name(ctype))
        } else {
            access.to_string()
        }
    }
}
