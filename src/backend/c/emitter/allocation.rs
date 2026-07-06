use super::*;

impl<'a> CEmitter<'a> {
    pub(super) fn collect_outputs<'t>(
        &self,
        tops: &'t [TopLevel<'_>],
        include_eval: bool,
        include_expr: bool,
    ) -> Vec<&'t Term<'t>> {
        let mut outputs = Vec::new();
        for top in tops {
            match top {
                TopLevel::TLEval(term, _) if include_eval => outputs.push(*term),
                TopLevel::TLExpr(term, _) if include_expr => outputs.push(*term),
                _ => {}
            }
        }
        outputs
    }

    pub(super) fn resolve_global_allocator(
        &self,
        raw_defs: &[TopLevel<'_>],
        allocation_required: bool,
    ) -> Result<Option<GlobalAllocator>, Diagnostic> {
        let mut found = Vec::new();
        for raw_def in raw_defs {
            let TopLevel::TLDef(name, _params, _ret, body, _) = raw_def else {
                continue;
            };
            if !name.starts_with(GLOBAL_ALLOCATOR_NAME_PREFIX) {
                continue;
            }
            found.push((*name, *body));
        }
        if found.len() > 1 {
            return Err(Diagnostic::new(
                "multiple #[global_allocator] definitions are not allowed",
            ));
        }
        if let Some((encoded_name, body)) = found.into_iter().next() {
            return self.allocator_from_definition(encoded_name, body).map(Some);
        }
        if !allocation_required {
            return Ok(None);
        }
        match self.options.target {
            CTarget::Hosted => Ok(Some(GlobalAllocator::hosted_default())),
            CTarget::BareMetal => Err(Diagnostic::new(
                "bare-metal target requires an explicit #[global_allocator]",
            )),
        }
    }

    fn allocator_from_definition(
        &self,
        encoded_name: &str,
        body: &Term<'_>,
    ) -> Result<GlobalAllocator, Diagnostic> {
        let instance_name = encoded_name
            .strip_prefix(GLOBAL_ALLOCATOR_NAME_PREFIX)
            .unwrap_or(encoded_name);
        let body = self.peel_annotations(body);
        let Term::StructCons(_, fields) = body else {
            return Ok(GlobalAllocator {
                allocate: self
                    .name_resolver
                    .escape(&format!("{instance_name}_allocate")),
                deallocate: self
                    .name_resolver
                    .escape(&format!("{instance_name}_deallocate")),
                reallocate: self
                    .name_resolver
                    .escape(&format!("{instance_name}_reallocate")),
                is_default: false,
            });
        };
        if fields.len() < 3 {
            return Err(Diagnostic::new(format!(
                "#[global_allocator] `{instance_name}` must provide allocate, deallocate, and reallocate"
            )));
        }
        Ok(GlobalAllocator {
            allocate: self.allocator_field_name(fields[0], "allocate")?,
            deallocate: self.allocator_field_name(fields[1], "deallocate")?,
            reallocate: self.allocator_field_name(fields[2], "reallocate")?,
            is_default: false,
        })
    }

    pub(super) fn peel_annotations<'t>(&self, mut term: &'t Term<'t>) -> &'t Term<'t> {
        while let Term::Annot(inner, _) | Term::Unsafe(inner) | Term::Pure(inner) = term {
            term = inner;
        }
        term
    }

    fn allocator_field_name(&self, term: &Term<'_>, field: &str) -> Result<String, Diagnostic> {
        match self.peel_annotations(term) {
            Term::Builtin(name) | Term::Global(name) => Ok(self.name_resolver.escape(name)),
            other => Err(Diagnostic::new(format!(
                "#[global_allocator] field `{field}` must be a direct function name, got {other:?}"
            ))),
        }
    }

    pub(super) fn term_requires_allocation(&self, term: &Term<'_>) -> bool {
        match term {
            Term::App(f, _)
                if self.is_string_concat_app(term) || self.term_requires_allocation(f) =>
            {
                true
            }
            Term::App(f, a) => self.term_requires_allocation(f) || self.term_requires_allocation(a),
            Term::Let(_, val, body, c) => {
                self.term_requires_allocation(val)
                    || self.term_requires_allocation(body)
                    || c.is_some_and(|c| self.term_requires_allocation(c))
            }
            Term::IfThenElse(c, t, f) => {
                self.term_requires_allocation(c)
                    || self.term_requires_allocation(t)
                    || self.term_requires_allocation(f)
            }
            Term::Annot(inner, c) => {
                self.term_requires_allocation(inner) || self.term_requires_allocation(c)
            }
            Term::Unsafe(inner) | Term::Pure(inner) | Term::Lam(inner) => {
                self.term_requires_allocation(inner)
            }
            Term::StructCons(name, values) => {
                self.struct_requires_heap_field(name)
                    || values
                        .iter()
                        .any(|value| self.term_requires_allocation(value))
            }
            Term::Variant(uname, idx, values) => {
                self.variant_requires_heap_payload(uname, *idx)
                    || values
                        .iter()
                        .any(|value| self.term_requires_allocation(value))
            }
            Term::StructProj(subject, _) => self.term_requires_allocation(subject),
            Term::Match(scrut, branches) => {
                self.term_requires_allocation(scrut)
                    || branches.iter().any(|(_, binds, body)| {
                        self.term_requires_allocation(body)
                            || binds.iter().any(|(_, c)| self.term_requires_allocation(c))
                    })
            }
            _ => false,
        }
    }

    pub(super) fn variant_requires_heap_payload(&self, uname: &str, idx: usize) -> bool {
        self.type_analyzer
            .enum_map()
            .get(uname)
            .and_then(|info| info.variants.get(idx))
            .is_some_and(|variant| variant.fields.iter().any(|field| field.boxed))
    }

    pub(super) fn struct_requires_heap_field(&self, sname: &str) -> bool {
        self.type_analyzer
            .struct_map()
            .get(sname)
            .is_some_and(|info| info.fields.iter().any(|field| field.boxed))
    }

    fn is_string_concat_app(&self, term: &Term<'_>) -> bool {
        let Term::App(f, right) = term else {
            return false;
        };
        let Term::App(prim, left) = *f else {
            return false;
        };
        matches!(*prim, Term::PrimOp(PrimOp::Add))
            && self.term_is_string_like(left)
            && self.term_is_string_like(right)
    }

    fn term_is_string_like(&self, term: &Term<'_>) -> bool {
        match term {
            Term::LitStr(_) => true,
            Term::Annot(_, constraint) => {
                matches!(**constraint, Term::Builtin("str") | Term::Global("str"))
            }
            Term::Unsafe(inner) | Term::Pure(inner) => self.term_is_string_like(inner),
            Term::App(_, _) if self.is_string_concat_app(term) => true,
            Term::Builtin(name) | Term::Global(name) => self
                .fun_sigs
                .iter()
                .find(|(n, _)| *n == *name)
                .is_some_and(|(_, sig)| sig.ret_type == CType::Str),
            _ => false,
        }
    }

    pub(super) fn emit_default_allocator(out: &mut String) {
        out.push_str(
            "static void* ligare_default_allocate(size_t size) { return malloc(size); }\n",
        );
        out.push_str("static void ligare_default_deallocate(void* ptr) { free(ptr); }\n");
        out.push_str(
            "static void* ligare_default_reallocate(void* ptr, size_t size) { return realloc(ptr, size); }\n\n",
        );
    }

    pub(super) fn should_emit_zero_arg_getter(&self, body: &Term<'_>) -> bool {
        !self.term_is_static_initializer(body)
    }

    fn term_is_static_initializer(&self, term: &Term<'_>) -> bool {
        match self.peel_annotations(term) {
            Term::LitInt(_) | Term::LitBool(_) | Term::LitStr(_) => true,
            Term::StructCons(name, values) => {
                !self.struct_requires_heap_field(name)
                    && values
                        .iter()
                        .all(|value| self.term_is_static_initializer(value))
            }
            Term::Variant(uname, idx, payloads) => {
                !self.variant_requires_heap_payload(uname, *idx)
                    && payloads
                        .iter()
                        .all(|value| self.term_is_static_initializer(value))
            }
            _ => false,
        }
    }

    pub(super) fn indent_block(block: &str, prefix: &str) -> String {
        block
            .lines()
            .map(|line| {
                let mut out = String::with_capacity(prefix.len() + line.len() + 1);
                out.push_str(prefix);
                out.push_str(line);
                out.push('\n');
                out
            })
            .collect()
    }
}
