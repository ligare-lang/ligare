//! C type system for code generation.
//!
//! Defines the `TypeMapper` trait for Ligare→C type resolution and the
//! `TypeAnalyzer` struct that builds C type maps, analyzes dependencies,
//! and emits typedefs — all as methods on a single cohesive object.

use crate::backend::ir::CType;
use crate::core::syntax::{Name, Term};
use crate::diagnostic::Diagnostic;
use std::collections::{HashMap, HashSet};

// ── Type info structs ──

/// Info about an enum variant for C codegen.
#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub name: String,
    pub fields: Vec<(String, CType)>,
}

/// Enum type info for C codegen.
#[derive(Debug, Clone)]
pub struct EnumInfo {
    pub variants: Vec<VariantInfo>,
}

/// Struct type info for C codegen.
#[derive(Debug, Clone)]
pub struct StructInfo {
    pub fields: Vec<(String, CType)>,
}

// ── TypeMapper trait ──

/// Maps Ligare type constraints to C types.
///
/// This trait abstracts the type resolution strategy, allowing different
/// backends or testing scenarios to plug in custom mappings.
pub trait TypeMapper {
    /// Map a constraint Term to its C type.
    fn constraint_to_ctype(&self, t: &Term<'_>) -> Result<CType, Diagnostic>;

    /// Returns true if the constraint marks an erased generic parameter.
    fn is_erased_parameter_constraint(&self, t: &Term<'_>) -> bool;
}

// ── TypeAnalyzer ──

/// Analyzes and emits C type definitions.
///
/// Owns the type name sets and the built maps; all type-related operations
/// are methods on this struct (OOP encapsulation).
pub struct TypeAnalyzer {
    /// Set of enum type names.
    enum_names: HashSet<String>,
    /// Set of struct type names.
    struct_names: HashSet<String>,
    /// Enum type info keyed by name.
    enum_map: HashMap<String, EnumInfo>,
    /// Struct type info keyed by name.
    struct_map: HashMap<String, StructInfo>,
}

impl TypeAnalyzer {
    /// Build a type analyzer from raw type definitions.
    pub fn new(
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
    ) -> Result<Self, Diagnostic> {
        let enum_names: HashSet<String> = enum_types.iter().map(|(n, _)| n.to_string()).collect();
        let struct_names: HashSet<String> =
            struct_types.iter().map(|(n, _)| n.to_string()).collect();
        let enum_map = Self::build_enum_map(enum_types, &enum_names, &struct_names)?;
        let struct_map = Self::build_struct_map(struct_types, &enum_names, &struct_names)?;
        Ok(Self {
            enum_names,
            struct_names,
            enum_map,
            struct_map,
        })
    }

    // ── Map builders (private) ──

    fn build_struct_map(
        struct_types: &[(&str, &Term<'_>)],
        enum_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<HashMap<String, StructInfo>, Diagnostic> {
        let mut map = HashMap::new();
        for (name, sdef) in struct_types {
            if let Term::StructDef(_, fields) = sdef {
                let fs: Vec<(String, CType)> = fields
                    .iter()
                    .map(|(fnm, fc)| {
                        Self::constraint_to_ctype_static(fc, enum_names, struct_names)
                            .map(|ct| (fnm.to_string(), ct))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                map.insert(name.to_string(), StructInfo { fields: fs });
            }
        }
        Ok(map)
    }

    fn build_enum_map(
        enum_types: &[(&str, &Term<'_>)],
        enum_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<HashMap<String, EnumInfo>, Diagnostic> {
        let mut map = HashMap::new();
        for (name, udef) in enum_types {
            if let Term::EnumDef(_, variants) = udef {
                let mut vis = Vec::new();
                for (vname, fields) in variants.iter() {
                    let fs: Vec<(String, CType)> = fields
                        .iter()
                        .map(|(fnm, fc)| -> Result<(String, CType), Diagnostic> {
                            let cty =
                                Self::constraint_to_ctype_static(fc, enum_names, struct_names)?;
                            let cty = if matches!(&cty, CType::Enum(un) if un == *name) {
                                CType::Ptr(Box::new(cty))
                            } else {
                                cty
                            };
                            Ok((fnm.to_string(), cty))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    vis.push(VariantInfo {
                        name: vname.to_string(),
                        fields: fs,
                    });
                }
                map.insert(name.to_string(), EnumInfo { variants: vis });
            }
        }
        Ok(map)
    }

    // ── Type dependency analysis ──

    /// Extract type dependencies from a type definition (struct or enum).
    pub fn type_dependencies(&self, def: &Term<'_>) -> HashSet<String> {
        let mut deps = HashSet::new();
        let fields: Option<&[(Name<'_>, &Term<'_>)]> = match def {
            Term::StructDef(_, f) => Some(*f),
            Term::EnumDef(_, variants) => {
                let all: Vec<_> = variants
                    .iter()
                    .flat_map(|(_, fields)| fields.iter().map(|(n, t)| (*n, *t)))
                    .collect();
                if all.is_empty() {
                    return deps;
                }
                for (_name, fty) in &all {
                    self.collect_type_refs(fty, &mut deps);
                }
                return deps;
            }
            _ => return deps,
        };
        if let Some(fs) = fields {
            for (_name, fty) in fs {
                self.collect_type_refs(fty, &mut deps);
            }
        }
        deps
    }

    /// Recursively collect user-defined type names from a constraint term.
    fn collect_type_refs(&self, t: &Term<'_>, deps: &mut HashSet<String>) {
        match t {
            Term::Builtin(name) | Term::Global(name) => {
                let s = name.to_string();
                if self.enum_names.contains(&s) || self.struct_names.contains(&s) {
                    deps.insert(s);
                }
            }
            Term::Pi(_, a, b) => {
                self.collect_type_refs(a, deps);
                self.collect_type_refs(b, deps);
            }
            Term::App(f, a) => {
                self.collect_type_refs(f, deps);
                self.collect_type_refs(a, deps);
            }
            _ => {}
        }
    }

    // ── Typedef emission ──

    /// Emit a C typedef for an enum type (tagged enum).
    pub fn emit_enum_typedef(&self, name: &str, udef: &Term<'_>) -> Result<String, Diagnostic> {
        let Term::EnumDef(_, variants) = udef else {
            return Ok(String::new());
        };
        let mut out = format!("// {name}\n");
        out.push_str(&format!("typedef struct {name} {{\n"));
        out.push_str("    int tag;\n");
        out.push_str("    union {\n");
        let info = self
            .enum_map
            .get(name)
            .ok_or_else(|| Diagnostic::new(format!("Cannot emit unknown enum typedef `{name}`")))?;
        for (variant_idx, (vname, fields)) in variants.iter().enumerate() {
            if fields.is_empty() {
                out.push_str(&format!("        struct {{ char _empty; }} {vname};\n"));
            } else {
                let vi = info.variants.get(variant_idx);
                out.push_str("        struct { ");
                for (field_idx, (fname, fty)) in fields.iter().enumerate() {
                    let cty = vi
                        .and_then(|variant| variant.fields.get(field_idx).map(|(_, cty)| cty))
                        .cloned()
                        .unwrap_or(self.constraint_to_ctype(fty)?);
                    out.push_str(&format!("{} {}; ", cty.c_name(), fname));
                }
                out.push_str(&format!("}} {vname};\n"));
            }
        }
        out.push_str("    } data;\n");
        out.push_str(&format!("}} {name};\n"));
        Ok(out)
    }

    /// Emit a C typedef for a struct type (product type with named fields).
    pub fn emit_struct_typedef(&self, name: &str, sdef: &Term<'_>) -> Result<String, Diagnostic> {
        let Term::StructDef(_, fields) = sdef else {
            return Ok(String::new());
        };
        let mut out = format!("// struct {name}\n");
        out.push_str(&format!("typedef struct {name} {{\n"));
        for (fname, fty) in fields.iter() {
            let cty = self.constraint_to_ctype(fty)?;
            out.push_str(&format!("    {} {};\n", cty.c_name(), fname));
        }
        out.push_str(&format!("}} {name};\n"));
        Ok(out)
    }

    /// Emit a struct typedef using pointers for enum-typed fields (for cyclic deps).
    pub fn emit_struct_typedef_ptr(
        &self,
        name: &str,
        sdef: &Term<'_>,
    ) -> Result<String, Diagnostic> {
        let Term::StructDef(_, fields) = sdef else {
            return Ok(String::new());
        };
        let mut out = format!("// struct {name} (ptr cycle)\n");
        out.push_str(&format!("typedef struct {name} {{\n"));
        for (fname, fty) in fields.iter() {
            let cty = self.constraint_to_ctype(fty)?;
            if matches!(cty, CType::Enum(_)) {
                out.push_str(&format!("    {}* {};\n", cty.c_name(), fname));
            } else {
                out.push_str(&format!("    {} {};\n", cty.c_name(), fname));
            }
        }
        out.push_str(&format!("}} {name};\n"));
        Ok(out)
    }

    /// Emit forward declarations and topological-sorted type definitions.
    pub fn emit_type_declarations(
        &self,
        out: &mut String,
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
    ) -> Result<(), Diagnostic> {
        // Forward declarations
        for (name, _) in struct_types {
            out.push_str(&format!("typedef struct {name} {name};\n"));
        }
        for (name, _) in enum_types {
            out.push_str(&format!("typedef struct {name} {name};\n"));
        }
        out.push('\n');

        // Topological sort
        let mut emitted: HashSet<String> = HashSet::new();
        let mut remaining: Vec<(&str, &Term<'_>, bool)> = Vec::new();
        for (n, s) in struct_types {
            remaining.push((n, *s, true));
        }
        for (n, u) in enum_types {
            remaining.push((n, *u, false));
        }

        let mut changed = true;
        while changed && !remaining.is_empty() {
            changed = false;
            let mut next: Vec<(&str, &Term<'_>, bool)> = Vec::new();
            for (name, def, is_struct) in remaining.drain(..) {
                let deps = self.type_dependencies(def);
                let all_deps_emitted = deps.iter().all(|d| emitted.contains(d.as_str()));
                if all_deps_emitted || deps.is_empty() {
                    if is_struct {
                        out.push_str(&self.emit_struct_typedef(name, def)?);
                    } else {
                        out.push_str(&self.emit_enum_typedef(name, def)?);
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

        // Handle cyclic dependencies
        if !remaining.is_empty() {
            for (name, def, is_struct) in remaining {
                if is_struct {
                    out.push_str(&self.emit_struct_typedef_ptr(name, def)?);
                } else {
                    out.push_str(&self.emit_enum_typedef(name, def)?);
                }
                out.push('\n');
            }
        }
        Ok(())
    }

    // ── Static helper (for map construction during Self::new) ──

    fn constraint_to_ctype_static(
        t: &Term<'_>,
        enum_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<CType, Diagnostic> {
        crate::backend::ir::constraint_to_ctype(t, enum_names, struct_names)
    }

    // ── Public accessors ──

    /// Access the enum type map.
    pub fn enum_map(&self) -> &HashMap<String, EnumInfo> {
        &self.enum_map
    }

    /// Access the struct type map.
    pub fn struct_map(&self) -> &HashMap<String, StructInfo> {
        &self.struct_map
    }
}

// ── TypeMapper implementation ──

impl TypeMapper for TypeAnalyzer {
    fn constraint_to_ctype(&self, t: &Term<'_>) -> Result<CType, Diagnostic> {
        crate::backend::ir::constraint_to_ctype(t, &self.enum_names, &self.struct_names)
    }

    fn is_erased_parameter_constraint(&self, t: &Term<'_>) -> bool {
        crate::backend::ir::is_erased_parameter_constraint(t)
    }
}
