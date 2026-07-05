use bumpalo::Bump;
use ligare::backend::c::emit_c;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    let a = TermArena::new(b);
    (b, a)
}

#[test]
fn interface_definition_instance_and_implicit_resolution() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def ShowInt : prop := struct
  show : int -> str

def show_int (x : int) : str := "int"
instance showInt : ShowInt := ShowInt.mk show_int

def render {s : ShowInt} (x : int) : str := ShowInt.show s x
#check render 1 : str
"#,
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn generic_interface_infers_type_and_instance_from_argument() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def Show (A : prop) : prop := struct
  show : A -> str

def show_int (x : int) : str := "int"
instance showInt : Show int := Show.mk show_int

def render {A : prop} {s : Show A} (x : A) : str := Show.show s x
#check render 1 : str
"#,
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn interface_default_method_can_be_composed() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def EqInt : prop := struct
  eq : int -> int -> bool

def eq_int (x : int) (y : int) : bool := x == y
instance eqInt : EqInt := EqInt.mk eq_int

def ne_default {e : EqInt} (x : int) (y : int) : bool := if EqInt.eq e x y then false else true
def ne_int (x : int) (y : int) : bool := ne_default x y
#check ne_int 1 2 : bool
"#,
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn missing_instance_reports_clear_error() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def ShowInt : prop := struct
  show : int -> str

def render {s : ShowInt} (x : int) : str := ShowInt.show s x
#check render 1 : str
"#,
    );
    let err = result.expect_err("missing instance should fail");
    assert!(
        err.message
            .contains("missing implicit instance for ShowInt"),
        "{}",
        err.message
    );
}

#[test]
fn implicit_instance_erases_to_static_function_call_in_c() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            r#"
def ShowInt : prop := struct
  show : int -> str

def show_int (x : int) : str := "int"
instance showInt : ShowInt := ShowInt.mk show_int

def render {s : ShowInt} (x : int) : str := ShowInt.show s x
def main : str := render 5
"#,
        )
        .expect("program should collect");
    let input = compiler.codegen_input();
    let c = emit_c(
        input.tops,
        input.raw_defs,
        input.fun_sigs,
        input.enum_types,
        input.struct_types,
    )
    .expect("C generation should succeed");
    assert!(c.contains("show_int(x)"), "{c}");
    assert!(c.contains("render__ShowInt__show_int(5)"), "{c}");
    assert!(!c.contains("struct ShowInt"), "{c}");
    assert!(!c.contains(".show"), "{c}");
}

#[test]
fn interface_method_call_desugars_through_instance() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def ShowInt : prop := struct
  show : int -> str

def show_int (x : int) : str := "int"
instance showInt : ShowInt := ShowInt.mk show_int

def render (x : int) : str := x.show
#check render 1 : str
"#,
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn interface_method_call_reports_ambiguity() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def ShowInt : prop := struct
  show : int -> str

def show_a (x : int) : str := "a"
def show_b (x : int) : str := "b"
instance showA : ShowInt := ShowInt.mk show_a
instance showB : ShowInt := ShowInt.mk show_b

def render (x : int) : str := x.show
"#,
    );
    let err = result.expect_err("ambiguous method should fail");
    assert!(
        err.message.contains("ambiguous method `show`"),
        "{}",
        err.message
    );
    assert!(err.message.contains("showA"), "{}", err.message);
    assert!(err.message.contains("showB"), "{}", err.message);
}

#[test]
fn of_nat_uses_expected_argument_type() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def OfNat (A : prop) : prop := struct
  of_nat : int -> A

def Peano : prop := enum
  | Zero
  | Succ of (pred : Peano)

#[terminating]
def from_int (n : int) : Peano :=
  if n <= 0 then Zero else Succ (from_int (n - 1))

instance of_nat_peano : OfNat Peano := OfNat.mk from_int

def accept_peano (x : Peano) : Peano := x
#check accept_peano 2 : Peano
"#,
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn add_instance_drives_infix_plus_for_user_struct() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def Add (A : prop) : prop := struct
  add : A -> A -> A

def Point : prop := struct
  x : int
  y : int

def point_add (a : Point) (b : Point) : Point :=
  Point.mk (std::primitive::int_add (Point.x a) (Point.x b)) (std::primitive::int_add (Point.y a) (Point.y b))

instance add_point : Add Point := Add.mk point_add

def sum (a : Point) (b : Point) : Point := a + b
#check sum (Point.mk 1 2) (Point.mk 3 4) : Point
"#,
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}
