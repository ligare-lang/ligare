use super::*;

impl<'a> ExpressionEmitter<'a> {
    pub fn emit_app(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let Term::App(f, a) = term else {
            unreachable!()
        };
        if let Some((op, left, right)) = Self::primop_binop_parts(term) {
            let left = self.emit_expr(left, ctx, enum_map, struct_map)?;
            let right = self.emit_expr(right, ctx, enum_map, struct_map)?;
            if op == PrimOp::Add && left.ctype == CType::Str && right.ctype == CType::Str {
                let left_code = self.value_code(left, enum_map)?;
                let right_code = self.value_code(right, enum_map)?;
                return Ok(CValue::code(
                    self.emit_string_concat(left_code.as_str(), right_code.as_str())?,
                    CType::Str,
                ));
            }
            let left_code = self.value_code(left, enum_map)?;
            let right_code = self.value_code(right, enum_map)?;
            return Ok(CValue::code(
                self.emit_binop(op, left_code.as_str(), right_code.as_str()),
                CType::Int64,
            ));
        }
        if matches!(Self::peel_expr_wrappers(f), Term::PrimOp(_)) {
            return self.emit_expr(a, ctx, enum_map, struct_map);
        }
        if let Some((target, pointer)) = Self::ptr_cast_parts(term) {
            return self.emit_ptr_cast(target, pointer, ctx, enum_map, struct_map);
        }
        let call = self.collect_call_args(term, ctx, enum_map, struct_map)?;
        let (param_types, ret_ty) = self
            .fun_sigs
            .iter()
            .find(|(n, _)| Some(*n) == call.raw_function.as_deref())
            .map(|(_, sig)| (sig.param_types.clone(), sig.ret_type.clone()))
            .ok_or_else(|| {
                Diagnostic::new(format!(
                    "Cannot emit call to `{}`; missing function signature",
                    call.function.as_str()
                ))
            })?;
        let args = if call.args.len() > param_types.len() {
            call.args[call.args.len() - param_types.len()..].to_vec()
        } else {
            call.args
        };
        let is_extern = call
            .raw_function
            .as_deref()
            .is_some_and(|name| self.extern_names.borrow().contains(name));
        let args = if is_extern {
            args.into_iter()
                .zip(param_types.iter())
                .map(|(arg, param_ty)| {
                    if self.ctype_requires_clone(param_ty) {
                        Ok(CCode::new(self.clone_value_expr(param_ty, arg.as_str())?))
                    } else {
                        Ok(arg)
                    }
                })
                .collect::<Result<Vec<_>, Diagnostic>>()?
        } else {
            args
        };
        let args = args
            .iter()
            .map(CCode::as_str)
            .collect::<Vec<_>>()
            .join(", ");
        let call_code = format!("{}({})", call.function.as_str(), args);
        let call_code = if is_extern && self.ctype_requires_clone(&ret_ty) {
            self.clone_value_expr(&ret_ty, &call_code)?
        } else {
            call_code
        };
        Ok(CValue::code(call_code, ret_ty))
    }

    fn primop_binop_parts<'term>(
        term: &'term Term<'term>,
    ) -> Option<(PrimOp, &'term Term<'term>, &'term Term<'term>)> {
        let Term::App(f, right) = term else {
            return None;
        };
        let Term::App(prim, left) = Self::peel_expr_wrappers(f) else {
            return None;
        };
        let Term::PrimOp(op) = Self::peel_expr_wrappers(prim) else {
            return None;
        };
        Some((*op, left, right))
    }

    fn peel_expr_wrappers<'term>(mut term: &'term Term<'term>) -> &'term Term<'term> {
        while let Term::Annot(inner, _) | Term::Unsafe(inner) | Term::Pure(inner) = term {
            term = inner;
        }
        term
    }

    fn ptr_cast_parts<'term>(
        term: &'term Term<'term>,
    ) -> Option<(&'term Term<'term>, &'term Term<'term>)> {
        let Term::App(f, pointer) = term else {
            return None;
        };
        let Term::App(head, target) = *f else {
            return None;
        };
        if matches!(*head, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_PTR_CAST))
        {
            Some((target, pointer))
        } else {
            None
        }
    }

    fn emit_ptr_cast(
        &self,
        target: &Term<'_>,
        pointer: &Term<'_>,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let pointer = self.emit_expr(pointer, ctx, enum_map, struct_map)?;
        let pointer_code = self.value_code(pointer, enum_map)?;
        let enum_names: HashSet<String> = enum_map.keys().cloned().collect();
        let struct_names: HashSet<String> = struct_map.keys().cloned().collect();
        let target_ty = CType::Ptr(Box::new(crate::backend::ir::constraint_to_ctype(
            target,
            &enum_names,
            &struct_names,
        )?));
        Ok(CValue::code(
            format!("(({}){})", target_ty.c_name(), pointer_code.as_str()),
            target_ty,
        ))
    }

    fn collect_call_args(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CallParts, Diagnostic> {
        match term {
            Term::App(f, a) => {
                let mut call = self.collect_call_args(f, ctx, enum_map, struct_map)?;
                let arg = self.emit_expr(a, ctx, enum_map, struct_map)?;
                call.args.push(self.value_code(arg, enum_map)?);
                Ok(call)
            }
            _ => {
                let raw_function = match term {
                    Term::Builtin(name) | Term::Global(name) => Some((*name).to_string()),
                    Term::Annot(Term::Builtin(name) | Term::Global(name), _) => {
                        Some((*name).to_string())
                    }
                    _ => None,
                };
                let value = self.emit_expr(term, ctx, enum_map, struct_map)?;
                Ok(CallParts {
                    raw_function,
                    function: self.value_code(value, enum_map)?,
                    args: Vec::new(),
                })
            }
        }
    }

    pub fn emit_binop(&self, op: PrimOp, left: &str, right: &str) -> String {
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
}
