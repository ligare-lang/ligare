use super::*;

impl ExpressionEmitter {
    pub(super) fn emit_struct_cons(
        &self,
        sname: &str,
        field_values: &[&Term<'_>],
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let type_name: String = sname.to_string();
        let Some(info) = struct_map.get(&type_name) else {
            return Err(Diagnostic::new(format!(
                "Cannot emit constructor for unknown struct `{type_name}`"
            )));
        };
        if field_values.len() != info.fields.len() {
            return Err(Diagnostic::new(format!(
                "Struct `{type_name}` expects {} field(s), got {}",
                info.fields.len(),
                field_values.len()
            )));
        }
        let field_codes: Vec<CCode> = info
            .fields
            .iter()
            .zip(field_values.iter())
            .map(|(field, value)| {
                let value = self.emit_expr(value, ctx, enum_map, struct_map)?;
                let code = self.value_code(value, enum_map)?;
                if field.boxed {
                    self.emit_heap_copy(&field.logical_type, code.as_str())
                } else {
                    Ok(code)
                }
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let field_codes = field_codes
            .iter()
            .map(CCode::as_str)
            .collect::<Vec<_>>()
            .join(", ");
        let c_type_name = CType::Struct(type_name.clone()).c_name();
        Ok(CValue::code(
            format!("(({}){{ {} }})", c_type_name, field_codes),
            CType::Struct(type_name),
        ))
    }

    pub(super) fn emit_struct_proj(
        &self,
        subject: &Term<'_>,
        idx: usize,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let subject = self.emit_expr(subject, ctx, enum_map, struct_map)?;
        let scode = self.value_code(subject.clone(), enum_map)?;
        let sty = subject.ctype;
        if let CType::Struct(ref sname) = sty
            && let Some(info) = struct_map.get(sname)
            && let Some(field) = info.fields.get(idx)
        {
            let access = format!("({}).{}", scode.as_str(), field.name);
            let code = if field.boxed {
                format!("*({access})")
            } else {
                access
            };
            return Ok(CValue::code(code, field.logical_type.clone()));
        }
        Err(Diagnostic::new(format!(
            "Cannot determine C type for struct projection field {idx} on {:?}",
            sty
        )))
    }

    pub(super) fn emit_variant(
        &self,
        uname: &str,
        idx: usize,
        payloads: &[&Term<'_>],
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let type_name: String = uname.to_string();
        let data_init =
            self.variant_data_init(&type_name, idx, payloads, ctx, enum_map, struct_map)?;
        let c_type_name = CType::Enum(type_name.clone()).c_name();
        Ok(CValue::code(
            format!(
                "(({}){{ .tag = {}, .data = {} }})",
                c_type_name, idx, data_init
            ),
            CType::Enum(type_name),
        ))
    }

    fn variant_data_init(
        &self,
        type_name: &str,
        idx: usize,
        payloads: &[&Term<'_>],
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<String, Diagnostic> {
        let info = enum_map.get(type_name).ok_or_else(|| {
            Diagnostic::new(format!(
                "Cannot emit variant {idx} for unknown enum `{type_name}`"
            ))
        })?;
        let vi = info.variants.get(idx).ok_or_else(|| {
            Diagnostic::new(format!(
                "Cannot emit variant {idx} for enum `{type_name}` with {} variant(s)",
                info.variants.len()
            ))
        })?;
        if payloads.len() != vi.fields.len() {
            return Err(Diagnostic::new(format!(
                "Variant `{}.{}` expects {} payload(s), got {}",
                type_name,
                vi.name,
                vi.fields.len(),
                payloads.len()
            )));
        }
        if vi.fields.is_empty() {
            return Ok(format!("{{ .{} = {{0}} }}", vi.name));
        }
        let field_inits: Vec<FieldInit> = vi
            .fields
            .iter()
            .zip(payloads.iter())
            .map(|(field, p)| {
                let value = self.emit_expr(p, ctx, enum_map, struct_map)?;
                let code = self.value_code(value.clone(), enum_map)?;
                let code = if field.boxed {
                    self.emit_heap_copy(&field.logical_type, code.as_str())?
                } else {
                    code
                };
                Ok(FieldInit {
                    field: field.name.clone(),
                    value: code,
                })
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let field_inits = field_inits
            .iter()
            .map(FieldInit::render)
            .collect::<Vec<_>>()
            .join(", ");
        Ok(format!("{{ .{} = {{ {} }} }}", vi.name, field_inits))
    }

    pub(super) fn emit_match(
        &self,
        scrut: &Term<'_>,
        branches: &[MatchBranch<'_>],
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let scrut_value = self.emit_expr(scrut, ctx, enum_map, struct_map)?;
        let sc = self.value_code(scrut_value.clone(), enum_map)?;
        let sc_ty = scrut_value.ctype;
        let scrut_enum = match &sc_ty {
            CType::Enum(name) => Some(name.as_str()),
            _ => None,
        };
        let mut cases = Vec::new();
        let mut ret_ty: Option<CType> = None;
        let enum_names: HashSet<String> = enum_map.keys().cloned().collect();
        let struct_names: HashSet<String> = struct_map.keys().cloned().collect();
        let type_names = TypeNameSets {
            enums: &enum_names,
            structs: &struct_names,
        };
        for (idx, binds, body) in branches.iter() {
            let mut branch_ctx = ctx.snapshot();
            for (bind_idx, (name, ty)) in binds.iter().enumerate().rev() {
                let cty =
                    self.match_bind_ctype(scrut_enum, *idx, bind_idx, ty, enum_map, &type_names)?;
                branch_ctx.push_binding(self.names.escape(name), cty);
            }
            let body_value = self.emit_expr(body, &mut branch_ctx, enum_map, struct_map)?;
            let bc = self.value_code(body_value.clone(), enum_map)?;
            if let Some(prev_ty) = &ret_ty {
                if prev_ty != &body_value.ctype {
                    return Err(Diagnostic::new(format!(
                        "Match branches return incompatible C types: {} and {}",
                        prev_ty.c_name(),
                        body_value.ctype.c_name()
                    )));
                }
            } else {
                ret_ty = Some(body_value.ctype.clone());
            }
            let mut case_binds = Vec::new();
            for (bind_idx, (name, ty)) in binds.iter().enumerate() {
                let cty =
                    self.match_bind_ctype(scrut_enum, *idx, bind_idx, ty, enum_map, &type_names)?;
                case_binds.push(MatchBind {
                    name: self.names.escape(name),
                    ctype: cty,
                });
            }
            cases.push(MatchCase {
                variant_idx: *idx,
                binds: case_binds,
                body_code: bc,
            });
        }
        let ret_ty = ret_ty.ok_or_else(|| {
            Diagnostic::new("Cannot determine C type for match expression without branches")
        })?;
        Ok(CValue::match_(MatchPlan {
            scrut_type: sc_ty,
            scrut_code: sc,
            ret_type: ret_ty.clone(),
            cases,
        }))
    }

    fn match_bind_ctype(
        &self,
        scrut_enum: Option<&str>,
        variant_idx: usize,
        bind_idx: usize,
        fallback_ty: &Term<'_>,
        enum_map: &HashMap<String, EnumInfo>,
        type_names: &TypeNameSets<'_>,
    ) -> Result<CType, Diagnostic> {
        if let Some(uname) = scrut_enum
            && let Some(info) = enum_map.get(uname)
            && let Some(variant) = info.variants.get(variant_idx)
            && let Some(field) = variant.fields.get(bind_idx)
        {
            return Ok(field.logical_type.clone());
        }
        crate::backend::ir::constraint_to_ctype(fallback_ty, type_names.enums, type_names.structs)
    }
}
