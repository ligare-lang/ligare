//! Stress-style integration tests for nested and boundary language constructs.
//!
//! These intentionally exercise supported README surface area through the
//! compiler pipeline without changing implementation behavior.

use bumpalo::Bump;
use ligare::backend::c::{emit_c, emit_eval_c};
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::front::parser::parse_program;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    let a = TermArena::new(b);
    (b, a)
}

#[track_caller]
fn assert_process_ok(source: &str) {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(source);
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[track_caller]
fn assert_process_err(source: &str, reason: &str) {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler.process_file_str(source).is_err(),
        "Expected error: {reason}"
    );
}

#[track_caller]
fn assert_parse_ok(source: &str) {
    let (bump, arena) = setup();
    let result = parse_program(source, bump, &arena);
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
}

fn collect_c(source: &str) -> String {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(source)
        .unwrap_or_else(|e| panic!("{e:?}"));
    emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"))
}

fn collect_eval_c(source: &str) -> String {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(source)
        .unwrap_or_else(|e| panic!("{e:?}"));
    emit_eval_c(compiler.codegen_input())
        .unwrap_or_else(|e| panic!("{e}"))
        .unwrap()
}

// Parser nesting and boundary cases.

#[test]
fn parse_deeply_nested_program_mix() {
    assert_parse_ok(
        "def Option : prop := enum\n  | None\n  | Some of (val : int)\n\
         def Box : prop := struct\n  value : Option\n  fallback : int\n\
         #check let b : Box := Box.mk (Some 5) 0 in match Box.value b with | None => Box.fallback b | Some x => x : int\n",
    );
}

#[test]
fn parse_match_branch_with_nested_match_body() {
    assert_parse_ok(
        "def Option : prop := enum\n  | None\n  | Some of (val : int)\n\
         #check match Some 1 with | None => 0 | Some x => match Some x with | None => -1 | Some y => y : int\n",
    );
}

#[test]
fn parse_large_enum_definition() {
    let variants = (0..32).map(|i| format!("  | V{i}\n")).collect::<String>();
    assert_parse_ok(&format!(
        "def Big : prop := enum\n{variants}#check V31 : Big\n"
    ));
}

#[test]
fn parse_wide_struct_definition() {
    let fields = (0..24)
        .map(|i| format!("  f{i} : int\n"))
        .collect::<String>();
    let args = (0..24).map(|i| i.to_string()).collect::<Vec<_>>().join(" ");
    assert_parse_ok(&format!(
        "def Wide : prop := struct\n{fields}#check Wide.mk {args} : Wide\n"
    ));
}

#[test]
fn parse_deep_arrow_type_with_parenthesized_domain() {
    assert_parse_ok(
        "def apply (f : (int -> int) -> int) (g : int -> int) : int := f g\n#check apply : ((int -> int) -> int) -> (int -> int) -> int\n",
    );
}

// Core expression checking.

#[test]
fn deeply_nested_let_if_arithmetic_checks() {
    assert_process_ok(
        "#check let a : int := 1 in let b : int := a + 2 in let c : int := b * 3 in if c > 0 then c + 4 else 0 : int\n",
    );
}

#[test]
fn nested_fun_application_with_mixed_param_annotations() {
    assert_process_ok(
        "def twice (f : int -> int) (x : int) : int := f (f x)\n\
         #check twice (fun (n : int) => n + 1) 40 : int\n",
    );
}

#[test]
fn curried_function_with_five_params_checks_order() {
    assert_process_ok(
        "def pick_middle (a : int) (b : bool) (c : str) (d : int) (e : bool) : str := c\n\
         #check pick_middle 1 true \"center\" 2 false : str\n",
    );
}

#[test]
fn curried_function_rejects_wrong_late_argument() {
    assert_process_err(
        "def pick_last (a : int) (b : bool) (c : int) : int := c\n#check pick_last 1 true false : int\n",
        "third argument should be int",
    );
}

#[test]
fn nested_refinement_success_through_let() {
    assert_process_ok(
        "def NonNeg := int where (x => x >= 0)\n#check let x : NonNeg := 0 in let y : NonNeg := x + 5 in y : int\n",
    );
}

#[test]
fn nested_refinement_failure_inside_let() {
    assert_process_err(
        "def NonNeg := int where (x => x >= 0)\n#check let x : NonNeg := 0 in let y : NonNeg := -1 in y : int\n",
        "negative literal should not satisfy NonNeg",
    );
}

#[test]
fn by_block_inside_nested_let_checks() {
    assert_process_ok(
        "#check let x : int by exact true := 5 in let y : int by exact true := x + 1 in y : int\n",
    );
}

// Struct nesting and destructuring.

#[test]
fn nested_structs_project_three_levels() {
    assert_process_ok(
        "def Point : prop := struct\n  x : int\n  y : int\n\
         def Segment : prop := struct\n  start : Point\n  end : Point\n\
         def Drawing : prop := struct\n  name : str\n  segment : Segment\n\
         def d : Drawing := Drawing.mk \"line\" (Segment.mk (Point.mk 1 2) (Point.mk 3 4))\n\
         #check Point.y (Segment.end (Drawing.segment d)) : int\n",
    );
}

#[test]
fn nested_destructuring_uses_inner_projection() {
    assert_process_ok(
        "def Point : prop := struct\n  x : int\n  y : int\n\
         def Segment : prop := struct\n  start : Point\n  end : Point\n\
         #eval let Segment{start, end} := Segment.mk (Point.mk 1 2) (Point.mk 3 4) in Point.x start + Point.y end\n",
    );
}

#[test]
fn destructuring_rejects_missing_field() {
    assert_process_err(
        "def Point : prop := struct\n  x : int\n  y : int\n#eval let Point{x, z} := Point.mk 1 2 in x\n",
        "field z is not part of Point",
    );
}

#[test]
fn struct_constructor_rejects_nested_wrong_field_type() {
    assert_process_err(
        "def Point : prop := struct\n  x : int\n  y : int\n\
         def Segment : prop := struct\n  start : Point\n  end : Point\n\
         #check Segment.mk (Point.mk 1 2) true : Segment\n",
        "end field should be Point",
    );
}

#[test]
fn wide_struct_construct_and_project_last_field() {
    let fields = (0..18)
        .map(|i| format!("  f{i} : int\n"))
        .collect::<String>();
    let args = (0..18).map(|i| i.to_string()).collect::<Vec<_>>().join(" ");
    assert_process_ok(&format!(
        "def Wide : prop := struct\n{fields}#check Wide.f17 (Wide.mk {args}) : int\n"
    ));
}

// Enum and match nesting.

#[test]
fn nested_enum_match_returns_inner_payload() {
    assert_process_ok(
        "def Option : prop := enum\n  | None\n  | Some of (val : int)\n\
         def Outer : prop := enum\n  | Empty\n  | Wrapped of (opt : Option)\n\
         #check match Wrapped (Some 9) with | Empty => 0 | Wrapped opt => match opt with | None => -1 | Some x => x : int\n",
    );
}

#[test]
fn match_branches_can_construct_structs() {
    assert_process_ok(
        "def Point : prop := struct\n  x : int\n  y : int\n\
         def Choice : prop := enum\n  | Origin\n  | At of (x : int) (y : int)\n\
         #check match At 3 4 with | Origin => Point.mk 0 0 | At x y => Point.mk x y : Point\n",
    );
}

#[test]
fn enum_constructor_rejects_payload_count_too_few() {
    assert_process_err(
        "def PairLike : prop := enum\n  | Both of (left : int) (right : int)\n#check Both 1 : PairLike\n",
        "Both needs two payload fields",
    );
}

#[test]
fn enum_constructor_rejects_payload_count_too_many() {
    assert_process_err(
        "def PairLike : prop := enum\n  | Both of (left : int) (right : int)\n#check Both 1 2 3 : PairLike\n",
        "Both has only two payload fields",
    );
}

#[test]
fn enum_constructor_rejects_payload_type_deep_in_args() {
    assert_process_err(
        "def Quad : prop := enum\n  | Q of (a : int) (b : bool) (c : str) (d : int)\n#check Q 1 true \"ok\" false : Quad\n",
        "fourth payload should be int",
    );
}

#[test]
fn recursive_enum_nested_value_checks() {
    assert_process_ok(
        "def Nat : prop := enum\n  | Zero\n  | Succ of (pred : Nat)\ndef three : Nat := Succ (Succ (Succ Zero))\n#check three : Nat\n",
    );
}

#[test]
fn nested_recursive_enum_match_function_checks() {
    assert_process_ok(
        "def Nat : prop := enum\n  | Zero\n  | Succ of (pred : Nat)\n\
         def is_zero (n : Nat) : bool := match n with | Zero => true | Succ p => false\n\
         def pred_or_zero (n : Nat) : Nat := match n with | Zero => Zero | Succ p => p\n\
         #check is_zero (pred_or_zero (Succ Zero)) : bool\n",
    );
}

#[test]
fn many_variant_enum_checks_last_variant() {
    let variants = (0..40).map(|i| format!("  | V{i}\n")).collect::<String>();
    assert_process_ok(&format!(
        "def Big : prop := enum\n{variants}#check V39 : Big\n"
    ));
}

// Generics and higher-order functions.

#[test]
fn nested_generic_identity_calls_across_types() {
    assert_process_ok(
        "def id (A : prop) (x : A) : A := x\n\
         #check id int (id int 5) : int\n\
         #check id bool (id bool true) : bool\n\
         #check id str (id str \"s\") : str\n",
    );
}

#[test]
fn generic_higher_order_application_checks() {
    assert_process_ok(
        "def apply_twice (A : prop) (f : A -> A) (x : A) : A := f (f x)\n\
         #check apply_twice int (fun (n : int) => n + 1) 0 : int\n",
    );
}

#[test]
fn generic_higher_order_rejects_wrong_function_domain() {
    assert_process_err(
        "def apply_twice (A : prop) (f : A -> A) (x : A) : A := f (f x)\n\
         #check apply_twice int (fun (b : bool) => b) 0 : int\n",
        "function domain should match selected type parameter",
    );
}

#[test]
fn generic_enum_nested_instance_checks() {
    assert_process_ok(
        "def Option (A : prop) : prop := enum\n  | None\n  | Some of (val : A)\n\
         def unwrap (A : prop) (opt : Option A) (default : A) : A := match opt with | None => default | Some x => x\n\
         #check unwrap int (Some (unwrap int (Some 7) 0)) 0 : int\n",
    );
}

// Code generation coverage for nested shapes.

#[test]
fn codegen_nested_structs_include_referenced_types_and_fields() {
    let source = "def Point : prop := struct\n  x : int\n  y : int\n\
         def Segment : prop := struct\n  start : Point\n  end : Point\n\
         def seg : Segment := Segment.mk (Point.mk 1 2) (Point.mk 3 4)\n#eval Point.x (Segment.start seg)\n";
    let c = collect_c(source);
    let eval_c = collect_eval_c(source);
    assert!(c.contains("typedef struct Point"), "{c}");
    assert!(c.contains("typedef struct Segment"), "{c}");
    assert!(c.contains("Point start;"), "{c}");
    assert!(c.contains("Point end;"), "{c}");
    assert!(eval_c.contains(".start"), "{eval_c}");
    assert!(eval_c.contains(".x"), "{eval_c}");
}

#[test]
fn codegen_nested_enum_match_uses_multiple_switches() {
    let c = collect_eval_c(
        "def Option : prop := enum\n  | None\n  | Some of (val : int)\n\
         def Outer : prop := enum\n  | Empty\n  | Wrapped of (opt : Option)\n\
         #eval match Wrapped (Some 9) with | Empty => 0 | Wrapped opt => match opt with | None => -1 | Some x => x\n",
    );
    let switch_count = c.matches("switch").count();
    assert!(
        switch_count >= 2,
        "expected nested matches to emit at least two switches:\n{c}"
    );
    assert!(c.contains("Option opt;"), "{c}");
}

#[test]
fn codegen_wide_struct_contains_all_fields() {
    let fields = (0..12)
        .map(|i| format!("  f{i} : int\n"))
        .collect::<String>();
    let args = (0..12).map(|i| i.to_string()).collect::<Vec<_>>().join(" ");
    let source = format!(
        "def Wide : prop := struct\n{fields}def w : Wide := Wide.mk {args}\n#eval Wide.f11 w\n"
    );
    let c = collect_c(&source);
    let eval_c = collect_eval_c(&source);
    for i in 0..12 {
        assert!(c.contains(&format!("int64_t f{i};")), "missing f{i}:\n{c}");
    }
    assert!(eval_c.contains(".f11"), "{eval_c}");
}
