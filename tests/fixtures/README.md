# Ligare test fixtures

## struct_basic.lig
Struct type feature tour:
- Point, Person, Flag, Wrapper struct definitions
- Construction via `Name.mk`
- Field projection via `Name.field`
- `#check` + `#show` with structs and fields

## struct_point.lig
Struct arithmetic:
- Vector-like operations on Point
- `add`, `scale`, `sum` functions
- Field comparison operators

## struct_nested.lig
Nested types:
- Struct inside union variant payload (Shape)
- Union inside struct field (Config)
- Mixed construction and `#show`

## color.lig
Non-recursive union demo (full pipeline: parse → check → C codegen):
- Enum-style union (Color)
- Pattern matching function (`to_int`)
- `#show` expressions compiled to native executable

## nat_peano.lig
Recursive Peano naturals (interpreter only):
- `Nat = Zero | Succ Nat`
- Nested variant construction
- Match with binding

## union_basic.lig
Union type feature tour:
- Enum + payload variants
- `#check` + `#show` with match

## union_single.lig
Minimal smoke test: single union definition.

## union_color.lig
Color enum union type.

## union_option.lig
Option type with payload and matching.

## Running

```sh
# Interpreter
cargo run -- tests/fixtures/struct_basic.lig

# Compile to native
cargo run -- tests/fixtures/struct_basic.lig -o test && ./test
```
