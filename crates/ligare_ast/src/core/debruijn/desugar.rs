use crate::config::{BUILTIN_DATA, BUILTIN_IO};
use crate::core::pool::TermArena;
use crate::core::syntax::{DoStmt, Name, Tactic, Term};

pub type VariantLookup<'bump> = (
    &'bump str,
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
);

pub struct Desugarer<'arena, 'bump> {
    arena: &'arena TermArena<'bump>,
}

#[derive(Clone, Copy)]
struct EffectContext;

impl<'arena, 'bump> Desugarer<'arena, 'bump> {
    pub fn new(arena: &'arena TermArena<'bump>) -> Self {
        Self { arena }
    }

    pub fn arena(&self) -> &'arena TermArena<'bump> {
        self.arena
    }

    pub fn desugar(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.try_desugar(t)
            .expect("desugar failed; use try_desugar for context-dependent parser nodes")
    }

    pub fn try_desugar(&self, t: &'bump Term<'bump>) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_without_variant_resolver(t, &[])
    }

    pub fn try_desugar_with_variant_resolver(
        &self,
        t: &'bump Term<'bump>,
        resolver: &impl Fn(&str) -> Option<VariantLookup<'bump>>,
    ) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_with_env(t, &[], Some(resolver), None)
    }

    pub fn desugar_with_names(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
    ) -> &'bump Term<'bump> {
        self.try_desugar_with_names(t, env)
            .expect("desugar failed; use try_desugar_with_names for context-dependent parser nodes")
    }

    pub fn try_desugar_with_names(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
    ) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_without_variant_resolver(t, env)
    }

    pub fn try_desugar_with_names_and_effect(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
        effect_constraint: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        let effect = self.effect_context(effect_constraint).ok_or_else(|| {
            "`do` block can only appear in a function returning an effect constraint".to_string()
        })?;
        self.try_desugar_with_env(t, env, Some(&no_variants), Some(effect))
    }

    pub fn try_desugar_with_names_and_variant_resolver(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
        resolver: &impl Fn(&str) -> Option<VariantLookup<'bump>>,
    ) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_with_env(t, env, Some(resolver), None)
    }

    pub fn try_desugar_with_names_variant_resolver_and_effect(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
        resolver: &impl Fn(&str) -> Option<VariantLookup<'bump>>,
        effect_constraint: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        let effect = self.effect_context(effect_constraint).ok_or_else(|| {
            "`do` block can only appear in a function returning an effect constraint".to_string()
        })?;
        self.try_desugar_with_env(t, env, Some(resolver), Some(effect))
    }

    fn try_desugar_without_variant_resolver(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
    ) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_with_env(t, env, Some(&no_variants), None)
    }

    fn try_desugar_with_env<R>(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
        resolver: Option<&R>,
        effect: Option<EffectContext>,
    ) -> Result<&'bump Term<'bump>, String>
    where
        R: Fn(&str) -> Option<VariantLookup<'bump>>,
    {
        let desugared = match t {
            Term::Named(name) => {
                if let Some(i) = env.iter().position(|n| *n == *name) {
                    self.arena.var(i)
                } else {
                    self.arena.global(name)
                }
            }
            Term::NamedLam(name, body) => {
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                self.arena
                    .lam(self.try_desugar_with_env(body, &ext, resolver, None)?)
            }
            Term::App(f, a) => self.arena.app(
                self.try_desugar_with_env(f, env, resolver, effect)?,
                self.try_desugar_with_env(a, env, resolver, effect)?,
            ),
            Term::Implicit(inner) => self
                .arena
                .implicit(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Lam(_) => t,
            Term::Pi(name, a, b) => {
                let a2 = self.try_desugar_with_env(a, env, resolver, effect)?;
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                let b2 = self.try_desugar_with_env(b, &ext, resolver, effect)?;
                self.arena.pi(name, a2, b2)
            }
            Term::Let(name, val, body, mc) => {
                let v2 = self.try_desugar_with_env(val, env, resolver, effect)?;
                let mc2 = mc
                    .map(|c| self.try_desugar_with_env(c, env, resolver, effect))
                    .transpose()?;
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                let b2 = self.try_desugar_with_env(body, &ext, resolver, effect)?;
                self.arena.let_(name, v2, b2, mc2)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                let c2 = self.try_desugar_with_env(cond, env, resolver, effect)?;
                let t2 = self.try_desugar_with_env(tbranch, env, resolver, effect)?;
                let f2 = self.try_desugar_with_env(fbranch, env, resolver, effect)?;
                self.arena.if_then_else(c2, t2, f2)
            }
            Term::Annot(inner, c) => self.arena.annot(
                self.try_desugar_with_env(inner, env, resolver, effect)?,
                self.try_desugar_with_env(c, env, resolver, effect)?,
            ),
            Term::ByProof(inner, tactics) => {
                let inner2 = inner
                    .map(|i| self.try_desugar_with_env(i, env, resolver, effect))
                    .transpose()?;
                let tactics2: Vec<_> = tactics
                    .iter()
                    .map(|tac| {
                        Ok(match tac {
                            Tactic::Exact(t) => {
                                Tactic::Exact(self.try_desugar_with_env(t, env, resolver, effect)?)
                            }
                            Tactic::Apply(t) => {
                                Tactic::Apply(self.try_desugar_with_env(t, env, resolver, effect)?)
                            }
                            Tactic::Intro(n) => Tactic::Intro(*n),
                            Tactic::Have(n, t) => Tactic::Have(
                                n,
                                self.try_desugar_with_env(t, env, resolver, effect)?,
                            ),
                            Tactic::Custom(n, args) => {
                                let args = args
                                    .iter()
                                    .map(|arg| {
                                        self.try_desugar_with_env(arg, env, resolver, effect)
                                    })
                                    .collect::<Result<Vec<_>, _>>()?;
                                Tactic::Custom(n, self.arena.alloc_slice(&args))
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena
                    .by_proof(inner2, self.arena.alloc_slice(&tactics2))
            }
            Term::Refine(name, parent, p) => {
                let p2 = self.try_desugar_with_env(parent, env, resolver, effect)?;
                let pred_with_param = self.arena.map(p, &|node| {
                    if let Term::Named(n) = node
                        && *n == *name
                    {
                        return Some(self.arena.ref_param());
                    }
                    None
                });
                let pred2 = self.try_desugar_with_env(pred_with_param, env, resolver, effect)?;
                self.arena.refine(name, p2, pred2)
            }
            Term::EnumDef(name, variants) => {
                let variants2: Vec<_> = variants
                    .iter()
                    .map(|(variant_name, fields)| {
                        let fields2 = fields
                            .iter()
                            .map(|(field_name, constraint)| {
                                Ok((
                                    *field_name,
                                    self.try_desugar_with_env(constraint, env, resolver, effect)?,
                                ))
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        Ok((*variant_name, self.arena.alloc_slice(&fields2)))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena
                    .enum_def(name, self.arena.alloc_slice(&variants2))
            }
            Term::StructDef(name, fields) => {
                let fields2 = fields
                    .iter()
                    .map(|(field_name, constraint)| {
                        Ok((
                            *field_name,
                            self.try_desugar_with_env(constraint, env, resolver, effect)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena
                    .struct_def(name, self.arena.alloc_slice(&fields2))
            }
            Term::Match(scrut, branches) => {
                let s2 = self.try_desugar_with_env(scrut, env, resolver, effect)?;
                let bs2: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let mut ext: Vec<&'bump str> = binds.iter().map(|(n, _)| *n).collect();
                        ext.extend_from_slice(env);
                        let b2 = self.try_desugar_with_env(body, &ext, resolver, effect)?;
                        let binds2: Vec<_> = binds
                            .iter()
                            .map(|(n, c)| {
                                Ok((*n, self.try_desugar_with_env(c, env, resolver, effect)?))
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        Ok((*idx, self.arena.alloc_slice(&binds2), b2))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena.match_(s2, self.arena.alloc_slice(&bs2))
            }
            Term::NamedMatch(scrut, branches) => {
                let s2 = self.try_desugar_with_env(scrut, env, resolver, effect)?;
                let resolver = resolver.ok_or_else(|| {
                    "cannot desugar named match without variant context".to_string()
                })?;
                let bs2: Vec<_> = branches
                    .iter()
                    .map(|(variant_name, binds, body)| {
                        let (_, idx, field_specs) = resolver(variant_name)
                            .ok_or_else(|| format!("unknown match variant: {}", variant_name))?;
                        let bind_specs: Vec<_> = binds
                            .iter()
                            .enumerate()
                            .map(|(i, (n, fallback))| {
                                let constraint =
                                    field_specs.get(i).map(|(_, c)| *c).unwrap_or(*fallback);
                                Ok((
                                    *n,
                                    self.try_desugar_with_env(
                                        constraint,
                                        env,
                                        Some(resolver),
                                        effect,
                                    )?,
                                ))
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        let mut ext: Vec<&'bump str> = binds.iter().map(|(n, _)| *n).collect();
                        ext.extend_from_slice(env);
                        let b2 = self.try_desugar_with_env(body, &ext, Some(resolver), effect)?;
                        Ok((idx, self.arena.alloc_slice(&bind_specs), b2))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena.match_(s2, self.arena.alloc_slice(&bs2))
            }
            Term::Variant(name, idx, payloads) => {
                let ps: Vec<_> = payloads
                    .iter()
                    .map(|p| self.try_desugar_with_env(p, env, resolver, effect))
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena.variant(name, *idx, self.arena.alloc_slice(&ps))
            }
            Term::StructCons(name, fields) => {
                let fs: Vec<_> = fields
                    .iter()
                    .map(|f| self.try_desugar_with_env(f, env, resolver, effect))
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena.struct_cons(name, self.arena.alloc_slice(&fs))
            }
            Term::NamedStructCons(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field, value)| {
                        Ok((
                            *field,
                            self.try_desugar_with_env(value, env, resolver, effect)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena
                    .named_struct_cons(*name, self.arena.alloc_slice(&fields))
            }
            Term::StructProj(subject, idx) => self.arena.struct_proj(
                self.try_desugar_with_env(subject, env, resolver, effect)?,
                *idx,
            ),
            Term::MethodCall(receiver, method) => self.arena.method_call(
                self.try_desugar_with_env(receiver, env, resolver, effect)?,
                method,
            ),
            Term::Do(stmts) => {
                let effect = effect.ok_or_else(|| {
                    "`do` block can only appear in a function returning an effect constraint"
                        .to_string()
                })?;
                self.desugar_do(stmts, env, resolver, effect)?
            }
            Term::Unsafe(inner) => self
                .arena
                .unsafe_(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Pure(inner) => self
                .arena
                .pure(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Quote(inner) => self
                .arena
                .quote(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Splice(inner) => self
                .arena
                .splice(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::Builtin(_)
            | Term::Global(_)
            | Term::AutoProof
            | Term::RefParam => t,
        };
        Ok(desugared)
    }

    fn desugar_do<R>(
        &self,
        stmts: &'bump [DoStmt<'bump>],
        env: &[&'bump str],
        resolver: Option<&R>,
        effect: EffectContext,
    ) -> Result<&'bump Term<'bump>, String>
    where
        R: Fn(&str) -> Option<VariantLookup<'bump>>,
    {
        let Some((last, prefix)) = stmts.split_last() else {
            return Err("do block must have at least one statement".to_string());
        };
        let mut ext_env = env.to_vec();
        for stmt in prefix {
            match stmt {
                DoStmt::Bind(name, _) | DoStmt::Let(name, _, _) => ext_env.insert(0, *name),
                DoStmt::Expr(_) => ext_env.insert(0, self.arena.alloc_str("_")),
            }
        }
        let mut body = match last {
            DoStmt::Expr(expr) => {
                self.try_desugar_with_env(expr, &ext_env, resolver, Some(effect))?
            }
            DoStmt::Let(..) | DoStmt::Bind(..) => {
                return Err("do block must end with a result expression".to_string());
            }
        };
        for stmt in prefix.iter().rev() {
            match stmt {
                DoStmt::Bind(name, rhs) => {
                    ext_env.remove(0);
                    let rhs = self.try_desugar_with_env(rhs, &ext_env, resolver, Some(effect))?;
                    body = self
                        .arena
                        .let_(name, rhs, body, Some(self.io_data_constraint()));
                }
                DoStmt::Let(name, rhs, mconstr) => {
                    ext_env.remove(0);
                    let rhs = self.try_desugar_with_env(rhs, &ext_env, resolver, Some(effect))?;
                    let c = mconstr
                        .map(|c| self.try_desugar_with_env(c, &ext_env, resolver, Some(effect)))
                        .transpose()?;
                    body = self.arena.let_(name, rhs, body, c);
                }
                DoStmt::Expr(expr) => {
                    ext_env.remove(0);
                    let expr = self.try_desugar_with_env(expr, &ext_env, resolver, Some(effect))?;
                    body = self.arena.let_(
                        self.arena.alloc_str("_"),
                        expr,
                        body,
                        Some(self.io_data_constraint()),
                    );
                }
            }
        }
        Ok(body)
    }

    fn effect_context(&self, constraint: &'bump Term<'bump>) -> Option<EffectContext> {
        self.effect_inner(constraint).map(|_| EffectContext)
    }

    fn effect_inner(&self, constraint: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        match constraint {
            Term::App(_, inner) => Some(inner),
            _ => None,
        }
    }

    fn io_data_constraint(&self) -> &'bump Term<'bump> {
        self.arena.app(
            self.arena.builtin(self.arena.alloc_str(BUILTIN_IO)),
            self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
        )
    }
}

fn no_variants<'bump>(_name: &str) -> Option<VariantLookup<'bump>> {
    None
}

pub fn desugar<'bump>(arena: &'bump TermArena<'bump>, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
    Desugarer::new(arena).desugar(t)
}
