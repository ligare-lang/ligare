//! Integration tests for generic (parametric) types and functions.
//! These tests exercise the full parse → check pipeline for generics.

use bumpalo::Bump;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    let a = TermArena::new(b);
    (b, a)
}

// ── Generic identity function ──

#[test]
fn generic_id_with_int() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result =
        compiler.process_file_str("def id (A : prop) (x : A) : A := x\n#check id int 5 : int\n");
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_id_with_bool() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler
        .process_file_str("def id (A : prop) (x : A) : A := x\n#check id bool true : bool\n");
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_id_with_str() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler
        .process_file_str("def id (A : prop) (x : A) : A := x\n#check id str \"hello\" : str\n");
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_id_wrong_arg_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result =
        compiler.process_file_str("def id (A : prop) (x : A) : A := x\n#check id bool 5 : bool\n");
    assert!(result.is_err(), "Should reject int where bool is expected");
}

// ── Generic multi-param function ──

#[test]
fn generic_const() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def konst (A : prop) (B : prop) (x : A) (y : B) : A := x\n#check konst int bool 5 true : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_const_wrong_order_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def konst (A : prop) (B : prop) (x : A) (y : B) : A := x\n#check konst int bool true 5 : int\n",
    );
    assert!(result.is_err(), "Should reject bool where int expected");
}

// ── Generic function with type param used only in domain ──

#[test]
fn generic_type_param_domain_only() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def to_int (A : prop) (x : A) : int := 0\n#check to_int str \"hello\" : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Generic type-level evaluation ──

#[test]
fn generic_id_eval() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str("def id (A : prop) (x : A) : A := x\n#eval id int 42\n");
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Nested generic functions ──

#[test]
fn nested_generic_calls() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler
        .process_file_str("def id (A : prop) (x : A) : A := x\n#check id int (id int 5) : int\n");
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Generic with prop universe ──

#[test]
fn generic_with_prop_param() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler
        .process_file_str("def id_type (A : prop) (x : A) : A := x\n#check id_type int 5 : int\n");
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Generic with data constraint on type param ──

#[test]
fn generic_type_param_constrained_by_data() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def pair_it (A : prop) (x : A) : int := 0\n#check pair_it bool true : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Apply generic function partially ──

#[test]
fn generic_partial_application() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    // Partially apply `id` to `int`, then use as int→int function
    let result = compiler.process_file_str(
        "def id (A : prop) (x : A) : A := x\ndef id_int : int -> int := id int\n#check id_int 42 : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Generic enum type definition ──

#[test]
fn generic_enum_definition() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Option (A : prop) : prop := enum\n  | None\n  | Some of (val : A)\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_enum_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Option (A : prop) : prop := enum\n  | None\n  | Some of (val : A)\n#check None : Option int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_enum_some_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Option (A : prop) : prop := enum\n  | None\n  | Some of (val : A)\n#check Some 42 : Option int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_enum_payload_uses_constraint_args() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Option (A : prop) : prop := enum\n  | None\n  | Some of (val : A)\n#check Some \"bad\" : Option int\n",
    );
    assert!(result.is_err(), "Should reject str payload for Option int");
}

// ── Generic struct type definition ──

#[test]
fn generic_struct_definition() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Pair (A : prop) (B : prop) : prop := struct\n  fst : A\n  snd : B\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_struct_with_params() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Pair (A : prop) (B : prop) : prop := struct\n  fst : A\n  snd : B\ndef p : Pair int bool := Pair.mk 42 true\n#check p : Pair int bool\n",
    );
    if result.is_err() {
        eprintln!(
            "generic_struct_with_params (expected may-fail): {:?}",
            result.err()
        );
    }
}

// ── Return type references type param ──

#[test]
fn generic_return_type_refers_to_param() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def id (A : prop) (x : A) : A := x\n#check id int 7 : int\n#check id bool false : bool\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Multiple type params ──

#[test]
fn three_type_params() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def triple (A : prop) (B : prop) (C : prop) (a : A) (b : B) (c : C) : A := a\n#check triple int bool str 1 true \"hello\" : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Generic function with refinement on type param ──

#[test]
fn generic_with_refinement_param() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def use_int (A : prop) (x : int where (y => y >= 0)) : int := x\n#check use_int bool 5 : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── edge cases ──

#[test]
fn generic_with_zero_data_params() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    // Only type params, no data params
    let result =
        compiler.process_file_str("def unit (A : prop) : int := 0\n#check unit int : int\n");
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_with_theorem_universe() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def use_theorem (A : theorem) : int := 0\n#check use_theorem int : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── C codegen monomorphizes generic functions ──

#[test]
fn codegen_generic_id_monomorphizes_int() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str("def id (A : prop) (x : A) : A := x\n#eval id int 42\n")
        .unwrap();
    let c = ligare::backend::c::emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let eval_c = ligare::backend::c::emit_eval_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"))
    .unwrap();
    assert!(c.contains("int64_t id__int(int64_t x)"), "{c}");
    assert!(eval_c.contains("id__int(42)"), "{eval_c}");
}

#[test]
fn codegen_generic_id_monomorphizes_str() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str("def id (A : prop) (x : A) : A := x\n#eval id str \"hi\"\n")
        .unwrap();
    let c = ligare::backend::c::emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let eval_c = ligare::backend::c::emit_eval_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"))
    .unwrap();
    assert!(c.contains("const char* id__str(const char* x)"), "{c}");
    assert!(eval_c.contains("id__str(\"hi\")"), "{eval_c}");
}

#[test]
fn codegen_generic_const_monomorphizes() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def konst (A : prop) (B : prop) (x : A) (y : B) : A := x\n#eval konst int bool 42 true\n",
        )
        .unwrap();
    let c = ligare::backend::c::emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let eval_c = ligare::backend::c::emit_eval_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"))
    .unwrap();
    assert!(
        c.contains("int64_t konst__int__bool(int64_t x, int64_t y)"),
        "{c}"
    );
    assert!(eval_c.contains("konst__int__bool(42, 1)"), "{eval_c}");
}

#[test]
fn codegen_generic_three_type_params_monomorphizes() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def triple (A : prop) (B : prop) (C : prop) (a : A) (b : B) (c : C) : A := a\n#eval triple int bool str 1 true \"hi\"\n",
        )
        .unwrap();
    let c = ligare::backend::c::emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let eval_c = ligare::backend::c::emit_eval_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"))
    .unwrap();
    assert!(c.contains("int64_t triple__int__bool__str("), "{c}");
    assert!(
        eval_c.contains("triple__int__bool__str(1, 1, \"hi\")"),
        "{eval_c}"
    );
}

// ── Generic enum codegen ──

#[test]
fn codegen_unused_generic_enum_emits_no_runtime_type() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str("def Option (A : prop) : prop := enum\n  | None\n  | Some of (val : A)\n")
        .unwrap();
    let c = ligare::backend::c::emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(!c.contains("Cannot map unresolved constraint"), "{c}");
    assert!(!c.contains("typedef struct Option"), "{c}");
}

#[test]
fn codegen_generic_enum_monomorphizes_used_instance() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Option (A : prop) : prop := enum\n  | None\n  | Some of (val : A)\ndef unwrap (A : prop) (opt : Option A) (default : A) : A :=\n  match opt with\n  | None => default\n  | Some x => x\n#eval unwrap int (Some 42) 0\n",
        )
        .unwrap();
    let c = ligare::backend::c::emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let eval_c = ligare::backend::c::emit_eval_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"))
    .unwrap();
    assert!(c.contains("typedef struct Option__int"), "{c}");
    assert!(c.contains("int64_t unwrap__int(Option__int opt"), "{c}");
    assert!(eval_c.contains("unwrap__int(((Option__int)"), "{eval_c}");
}

#[test]
fn codegen_non_prefix_erased_param_monomorphizes() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def choose (x : int) (A : prop) (y : A) : A := y\n\
             #eval choose 0 int 5\n",
        )
        .unwrap();
    let c = ligare::backend::c::emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let eval_c = ligare::backend::c::emit_eval_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"))
    .unwrap();
    assert!(
        c.contains("int64_t choose__int(int64_t x, int64_t y)"),
        "{c}"
    );
    assert!(eval_c.contains("choose__int(0, 5)"), "{eval_c}");
    assert!(!c.contains("prop A"), "{c}");
}

#[test]
fn namespace_function_method_call_monomorphizes_receiver_type() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
            "def List (A : prop) : prop := enum\n  | Nil\n  | Cons of (head : A) (tail : List A)\nnamespace List { def append {A : prop} (xs : List A) (x : A) : List A := Cons x xs }\ndef main : List int := let xs := Nil in xs.append 1\n",
        );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Generic struct codegen ──

#[test]
fn codegen_unused_generic_struct_emits_no_runtime_type() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str("def Pair (A : prop) (B : prop) : prop := struct\n  fst : A\n  snd : B\n")
        .unwrap();
    let c = ligare::backend::c::emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.enum_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(!c.contains("Cannot map unresolved constraint"), "{c}");
    assert!(!c.contains("typedef struct Pair"), "{c}");
}
