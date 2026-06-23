//! Integration tests for struct types (product types) and field projection.

use bumpalo::Bump;
use ligare::backend::c::emit_c;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    let a = TermArena::new(b);
    (b, a)
}

// ── Definition and basic checking ──

#[test]
fn struct_definition_and_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\n#check Point.mk 3 4 : Point\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_three_fields() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Triple : prop := struct\n  a : int\n  b : int\n  c : int\n#check Triple.mk 1 2 3 : Triple\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_field_types_enforced() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : str\n#check Point.mk 3 \"hello\" : Point\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_wrong_field_type_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\n#check Point.mk \"hi\" 4 : Point\n",
    );
    assert!(result.is_err(), "Should reject string for int field");
}

#[test]
fn struct_wrong_field_count_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\n#check Point.mk 3 : Point\n",
    );
    assert!(result.is_err(), "Should reject wrong field count");
}

#[test]
fn struct_wrong_type_for_struct_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler
        .process_file_str("def Point : prop := struct\n  x : int\n  y : int\n#check 5 : Point\n");
    assert!(result.is_err(), "Should reject int as struct");
}

// ── Field projection ──

#[test]
fn struct_field_projection() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\n#check Point.x (Point.mk 3 4) : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_projection_in_definition() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\ndef get_x (p : Point) : int := Point.x p\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_projection_wrong_type_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\n#check Point.x 5 : int\n",
    );
    assert!(result.is_err(), "Should reject projection from int");
}

#[test]
fn struct_second_field_projection() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\n#show Point.y (Point.mk 1 42)\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Struct as value ──

#[test]
fn named_struct_value() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\ndef p : Point := Point.mk 3 4\n#check p : Point\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_show_construction() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\n#show Point.mk 10 20\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_show_projection() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\n#show Point.x (Point.mk 7 8)\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_named_value_projection() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\ndef p : Point := Point.mk 5 6\n#show Point.x p\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_with_str_field() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Person : prop := struct\n  name : str\n  age : int\n#check Person.mk \"Alice\" 30 : Person\n#check Person.name (Person.mk \"Bob\" 25) : str\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_with_bool_field() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Flag : prop := struct\n  enabled : bool\n  value : int\n#check Flag.mk true 100 : Flag\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Struct with single field ──

#[test]
fn struct_single_field() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Wrapper : prop := struct\n  inner : int\n#check Wrapper.mk 42 : Wrapper\n#check Wrapper.inner (Wrapper.mk 99) : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── Struct in arithmetic ──

#[test]
fn struct_field_arithmetic() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\ndef add (p1 : Point) (p2 : Point) : Point := Point.mk (Point.x p1 + Point.x p2) (Point.y p1 + Point.y p2)\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_field_comparison() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\ndef origin : Point := Point.mk 0 0\n#show Point.x origin == 0\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

// ── C codegen for structs ──

#[test]
fn codegen_struct_typedef() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\ndef p : Point := Point.mk 3 4\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains("typedef struct Point"),
        "missing struct typedef:\n{c}"
    );
    assert!(c.contains("int64_t x;"), "missing x field:\n{c}");
    assert!(c.contains("int64_t y;"), "missing y field:\n{c}");
}

#[test]
fn codegen_struct_construction() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\ndef p : Point := Point.mk 3 4\n#show p\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("const Point p"), "missing struct const:\n{c}");
}

#[test]
fn codegen_struct_projection() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\n#show Point.x (Point.mk 7 8)\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains(".x"), "missing field name .x in codegen:\n{c}");
}

#[test]
fn codegen_struct_projection_uses_real_field_name() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\n#show Point.y (Point.mk 1 42)\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains(".y"), "missing real field name .y:\n{c}");
    assert!(
        !c.contains("_f"),
        "should not contain fallback _f prefix:\n{c}"
    );
}

#[test]
fn codegen_struct_function_param() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\ndef get_x (p : Point) : int := Point.x p\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains("int64_t get_x(Point"),
        "missing function with struct param:\n{c}"
    );
}

#[test]
fn codegen_struct_with_str_field() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Person : prop := struct\n  name : str\n  age : int\ndef p : Person := Person.mk \"Alice\" 30\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains("const char* name;"),
        "missing str field type:\n{c}"
    );
}

#[test]
fn codegen_struct_single_field() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Wrapper : prop := struct\n  inner : int\ndef w : Wrapper := Wrapper.mk 99\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains("typedef struct Wrapper"),
        "missing typedef:\n{c}"
    );
}

// ── Nested types: struct-in-union, union-in-struct ──

#[test]
fn union_with_struct_payload() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Point : prop := struct\n  x : int\n  y : int\ndef Shape : prop := union\n  | Circle of (center : Point) (r : int)\n  | Rect of (tl : Point) (br : Point)\ndef c : Shape := Circle (Point.mk 0 0) 5\n#check c : Shape\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn struct_with_union_field() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        "def Option : prop := union\n  | None\n  | Some of (val : int)\ndef Config : prop := struct\n  name : str\n  opt : Option\ndef c : Config := Config.mk \"test\" (Some 42)\n#check c : Config\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn codegen_union_with_struct_payload() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\ndef Shape : prop := union\n  | Circle of (center : Point) (r : int)\n  | Rect\ndef s : Shape := Circle (Point.mk 1 2) 5\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    // Union typedef should use Point struct as field type
    assert!(
        c.contains("Point center;"),
        "union variant should reference struct type:\n{c}"
    );
}

// ── Destructuring let ──

#[test]
fn let_destruct_basic() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\n#show let Point{x, y} := Point.mk 3 4 in x + y\n",
        );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn let_destruct_single_field() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
            "def Wrapper : prop := struct\n  inner : int\n#show let Wrapper{inner} := Wrapper.mk 42 in inner\n",
        );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn let_destruct_named_value() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\ndef p : Point := Point.mk 10 20\n#show let Point{x, y} := p in x * y\n",
        );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn let_destruct_three_fields() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
            "def Triple : prop := struct\n  a : int\n  b : int\n  c : int\n#show let Triple{a, b, c} := Triple.mk 1 2 3 in a + b + c\n",
        );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn let_destruct_in_function() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
            "def Point : prop := struct\n  x : int\n  y : int\ndef dist_sq (p : Point) : int := let Point{x, y} := p in x * x + y * y\n",
        );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn codegen_struct_with_union_field() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Option : prop := union\n  | None\n  | Some of (val : int)\ndef Config : prop := struct\n  name : str\n  opt : Option\ndef c : Config := Config.mk \"cfg\" (Some 99)\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    // Struct typedef should use Option union as field type
    assert!(
        c.contains("Option opt;"),
        "struct field should reference union type:\n{c}"
    );
}
