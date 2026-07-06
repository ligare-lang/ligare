use super::*;

impl<'bump> Compiler<'bump> {
    pub(super) fn process_eval_like(
        &self,
        term: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
        label: &str,
    ) -> Result<(), Diagnostic> {
        let resolved = self.try_resolve_all(term)?;
        self.checker
            .check(
                &empty_ctx(),
                resolved,
                self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
            )
            .map_err(|err| {
                Self::wrap_diagnostic(format!("{label} check failed"), err, span.clone())
            })?;
        if self.quiet {
            return Ok(());
        }
        let self_name = self
            .checker
            .desugar_with_context(term)
            .ok()
            .and_then(|term| self.extract_func_name(term));
        let mut ev = Evaluator::new(self.arena);
        if let Some(n) = self_name {
            ev.set_self_name(n);
        }
        match ev.eval(resolved) {
            Err(err) => Err(Diagnostic::with_span(
                format!("{label} error: {}", err),
                span,
            )),
            Ok(val) => {
                println!("{}", PrettyPrinter::pretty(val));
                Ok(())
            }
        }
    }

    pub(super) fn register_prop_definition(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> bool {
        match body {
            Term::EnumDef(..) => {
                if !self.quiet {
                    println!("[enum] {}", name);
                }
                let type_param_names: Vec<_> = params.iter().map(|(n, _)| *n).collect();
                let type_params = self.arena.alloc_slice(&type_param_names);
                self.checker.add_enum(name, body, type_params);
                if !params.is_empty() {
                    let term = self.desugar_top_def(name, params, m_ret, body);
                    self.env.insert(name, term);
                }
                true
            }
            Term::StructDef(..) => {
                if !self.quiet {
                    println!("[struct] {}", name);
                }
                let type_param_names: Vec<_> = params.iter().map(|(n, _)| *n).collect();
                let type_params = self.arena.alloc_slice(&type_param_names);
                self.checker.add_struct(name, body, type_params);
                if !params.is_empty() {
                    let term = self.desugar_top_def(name, params, m_ret, body);
                    self.env.insert(name, term);
                }
                true
            }
            _ if params.is_empty() => {
                let Some(desugared) = self.checker.desugar_with_context(body).ok() else {
                    return false;
                };
                if let Some((parent, predicate)) = Self::refinement_parts(desugared) {
                    if !self.quiet {
                        println!("[refinement] {}", name);
                    }
                    self.checker.add_refinement(name, parent, predicate);
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}
