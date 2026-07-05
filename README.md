# Ligare

> **Everything is a term. Everything is a constraint.**  
> File extension: `.lig`

[中文版](README_zh.md)

Ligare is an experimental programming language and compiler written in Rust. It explores a minimal core where values, types, propositions, proofs, functions, data declarations, and macros are all represented as terms constrained by other terms.

The current repository contains:

- A lexer, parser, type checker, evaluator, formatter, documentation generator, and C backend for `.lig` source files.
- A package mode driven by `ligare.toml`, with build, update, test, format, and documentation commands.
- Experimental support for refinement constraints, proof blocks, structs, enums, pattern matching, modules, generics, and code generation to C.
- A small `ligls` language-server crate under `crates/ligls`.

Ligare is still under active development. Some sections below describe intended language design; features explicitly marked as planned are not implemented yet.

## Quick Start

### Requirements

- Rust toolchain. The repository includes `rust-toolchain.toml`, so `rustup` will select the pinned toolchain automatically.
- A C compiler available as `cc` when using native output with `-o` or package builds.

### Build and Test

```bash
cargo build
cargo test
```

### Run a Source File

```bash
cargo run -- tests/fixtures/test.lig
cargo run -- tests/fixtures/test.lig --eval "1 + 2"
```

### Emit or Compile C

```bash
cargo run -- --emit-c tests/fixtures/test.lig
cargo run -- -o /tmp/ligare-test tests/fixtures/test.lig
```

### Build a Package

```bash
cargo run -- new hello
cargo run -- build examples/test
./examples/test/target/test
```

### Format Source

```bash
cargo run -- fmt .
cargo run -- fmt --check .
```

### Generate Markdown Docs

```bash
cargo run -- doc .
cargo run -- doc . -o docs/api.md
```

## CLI Reference

```text
Usage: ligare [OPTIONS] [FILES]... [COMMAND]
```

| Command or option | Description |
|-------------------|-------------|
| `ligare <files>` | Process one or more `.lig` files and run top-level checks/evaluations. |
| `--eval <EXPR>` | Evaluate an expression after processing the input files. |
| `--emit-c` | Emit C source code instead of running the evaluator. |
| `-o, --output <PATH>` | Compile generated C into a native executable at `PATH`. |
| `new [--bin\|--lib] PATH` | Create a new package directory with `ligare.toml` and a `src` entry file. |
| `build [PATH]` | Build the package found at `PATH` or the current directory. |
| `update [NAME] [VERSION]` | Refresh `ligare.lock`, optionally pinning one dependency. |
| `test [PATH]` | Run package files whose names end in `_test.lig`. |
| `fmt [--check] [PATH]` | Format `.lig` files, or check whether formatting is needed. |
| `doc [--private] [-o PATH] [PATH]` | Generate Markdown documentation from `.lig` files. |

## Package Manifest

Package builds use `ligare.toml`:

```toml
[package]
name = "test"
version = "0.1.0"
type = "binary"

[dependencies]
```

Supported package types are `binary` and `lib`. If `entry` is omitted, Ligare uses the default source entry for the package. Dependencies may point to Git repositories or local paths.

## Repository Layout

```text
src/front/        lexer and parser
src/core/         core term syntax, arena allocation, evaluation, desugaring
src/checker/      constraint checking, inference, proof search, erasure
src/compiler/     file/module pipeline, project loading, monomorphization
src/backend/      IR and C code generation
src/package/      manifest, lockfile, and dependency resolution
crates/ligare_fmt formatter crate
crates/ligare_doc markdown documentation generator crate
crates/ligls/     experimental language server crate
tests/            integration and regression tests
tests/fixtures/   sample .lig programs used by tests
examples/test/    example Ligare package
docs/             grammar notes
```

## 1. Core Philosophy

Ligare is a minimalist programming language. It recognizes only one kind of entity — the **Term**.  
There is no separate "type" syntax, no "type vs. value" dichotomy, and no "program vs. proof" dichotomy.  
Everything is a term, and every relationship is a **constraint**.

## 2. Terms and Constraints

### 2.1 Terms
A term is the only existence in the language. Variables, literals, functions, data types, propositions, proofs, macros... all are terms.

### 2.2 Constraints
Relationships between terms are established through **constraints**.  
`a : T` means that term `a` is constrained by term `T` (i.e., `a` has type `T`).  
The constraint relationship replaces the "type ascription" found in traditional languages, but constraints themselves are also terms and can be constrained by other terms.

**Example**  
```ligare
3 : int       -- 3 is constrained by int
int : prop    -- int is constrained by data
```

### 2.3 Levels
All terms have a level. Constraint relationships enforce level ordering to prevent Russell-paradox-style self-referential structures.  
(Specific level rules will be defined in detail in the formalization section.)

### 2.4 Naming Conventions
- **Constraints / Types**: PascalCase (e.g., `Nat`, `Point`, `LinkedList`)
- **Functions / Theorems**: snake_case (e.g., `div`, `is_sorted`, `add_node`)

## 3. Meta-Constraints

The language has four built-in root constraints, called **meta-constraints**. They define the foundation of the universe.

| Meta-constraint | Meaning | Exists at runtime? |
|-----------------|---------|---------------------|
| `data` | The computable data universe; all terms ultimately retained belong here | Yes |
| `prop` | The proposition universe, describing logical conditions | No (erased) |
| `theorem` | An established proposition, encapsulating a proof | No (erased) |
| `proof` | The concrete construction of a proof; an evidence term | No (erased) |

All user-defined constraints are ultimately rooted beneath these four meta-constraints.

## 4. Refinement Constraints (Where Clauses)

Users can define new constraints by refining an existing constraint with a predicate. This is Ligare's way of defining "subtypes."

**Syntax**  
```ligare
def nat := int where (x => x >= 0)
```

**Interpretation**  
`nat` is a new constraint. Any term constrained by `nat` must:
1. Be constrained by `int` (which itself is constrained by `data`);
2. Satisfy the predicate `x >= 0`.

**Usage**  
```ligare
def x : nat := 10
#check x : nat       -- passes
#check x : int       -- also passes (nat is a subtype of int)
#check -5 : nat      -- fails: -5 is not >= 0
```

The compiler automatically demands this proof where needed, or derives it from context.

Multiple refinements can coexist in the same program:
```ligare
def pos   := int where (x => x > 0)
def even  := int where (x => x % 2 = 0)
def ten   := int where (x => x = 10)
```

Refinements can also be used inline in function parameters:
```ligare
def sdiv (a : int) (b : int where (x => x /= 0)) : int := a / b
```

## 5. Functions

Functions are defined with `def` (or `func`), using curried parameter lists. They can constrain their own parameters via `where` clauses, forming pre-condition contracts.

**Syntax example**  
```ligare
def div (a : int) (b : int where (x => x /= 0)) : int := a / b
```

**Proof obligations**  
- The caller must provide a proof that `b /= 0` (or the compiler derives it automatically).
- The function body operates under the guarantee that the parameter constraints hold.

All proof terms (`proof`) are erased after passing compile-time checks, with zero runtime overhead.

**Function with no return type annotation**  
```ligare
def id (x : int) := x
```

**Recursive function**  
```ligare
def fib (n : int) : int :=
  if n < 2 then n else fib (n - 1) + fib (n - 2)
```

## 6. `if` Expressions and Theorem Introduction

The condition of an `if` is treated as a proposition. When entering a branch, the branch context automatically introduces a corresponding `theorem`.

**Example**  
```ligare
if x > 0 then
  -- a theorem: x > 0 is automatically available here
  -- it can be used to satisfy proof obligations of other constraints
  div 10 x  -- x /= 0 can be automatically derived from x > 0
else
  -- a theorem: not (x > 0) is automatically available here
```

After compilation, `if` is still compiled into a simple conditional jump; all proof parts are erased.

## 7. Proofs and Tactics (Lean 4-style `by` blocks)

Ligare supports interactive proof construction via `by` blocks with tactics, inspired by Lean 4.

**Simple proof with `exact`**  
```ligare
#check 5 by
  exact true : nat
```

**Multi-tactic proof with `intro`**  
```ligare
#check 0 by
  intro
  exact 0 : int -> int
```

**Standalone proof term (no subject)**  
```ligare
#check (by
  intro
  exact 0) : int -> int
```

**Applying a proof immediately**  
```ligare
#eval (by
  intro
  exact 0) 5
```

Available tactics:
- `exact <term>` — provide a term that satisfies the goal directly
- `intro [name]` — introduce a Pi-type hypothesis
- `apply <term>` — apply a function to reduce the goal
- `have <name> := <term>` — introduce a lemma

## 8. Expressions and Let Bindings

### Lambda expressions
```ligare
-- Legacy syntax (still supported)
\x. x + 1
\a. \b. a + b

-- New `fun` syntax (preferred)
fun x => x + 1
fun x y => x + y
fun (x : int) => x + 1
fun a (b : int) => a + b
```

### Let expressions
```ligare
let x := 5 in x + 3
let x : int := 5 in x
let x := 5 in let y := x + 1 in y * 2
```

### Type annotation
```ligare
(5 : int)
(5 : nat) by exact true
```

### Function (Pi) types
```ligare
int -> bool               -- non-dependent arrow
(x : int) -> x            -- dependent arrow
```

### Proposition combinators
```ligare
∧ P Q    -- conjunction: P ∧ Q
∨ P Q    -- disjunction: P ∨ Q
¬ P      -- negation: ¬P
```

## 9. Structs

A struct definition is a **constraint** — it lives in the `prop` universe and is erased after type checking.  Struct *values* (constructed instances) live in `data` and are retained at runtime.

A struct has named fields.  It is the **product type** (∧) of Ligare: all fields exist simultaneously.  Since refinement types (`where` clauses) already handle invariants, structs focus solely on bundling named data.

**Syntax**
```ligare
def Point : prop := struct
  x : int
  y : int
```

**Construction**
```ligare
def p : Point := Point.mk 3 4
```

**Field projection**
```ligare
#check Point.x p : int
def get_x (pt : Point) : int := Point.x pt
```

**How it works**
- `Point.mk` is an auto-generated constructor that takes field values in order.
- `Point.x` is an auto-generated projector that extracts the named field from a struct value.
- The compiler automatically generates these from the struct definition.
- Field constraints are verified at construction time.

**C representation**
```c
typedef struct Point {
    int64_t x;
    int64_t y;
} Point;
```

## 10. Enum Types

An enum definition is a **constraint** — it lives in the `prop` universe and is erased after type checking.  Enum *values* (variant instances) live in `data` and are retained at runtime.

An enum has named variants, each with optional payload fields.  It is the **sum type** (∨) of Ligare: exactly one variant holds at a time.

### 10.1 Definition

Enums use the `enum` keyword, symmetric with `struct`.  Each variant is introduced by `|`:

```ligare
-- Simple enumeration (no payload)
def Color : prop := enum
  | Red
  | Green
  | Blue

-- Polymorphic enum with payload
def Option (A : prop) : prop := enum
  | None
  | Some of (val : A)

-- Recursive enum — essential for compiler ASTs
def Expr : prop := enum
  | Lit  of (n : int)
  | Add  of (l : Expr) (r : Expr)
  | If   of (c : Expr) (t : Expr) (e : Expr)

-- Multi-field payload with named parameters
def Result (T : prop) (E : prop) : prop := enum
  | Ok  of (value : T)
  | Err of (error : E)
```

### 10.2 Construction

Variant names are constructor functions.  They are automatically generated from the enum definition:

```ligare
def c  : Color       := Red
def x  : Option int  := Some 5
def y  : Option int  := None              -- type annotation needed for inference
def e  : Expr        := Add (Lit 1) (Lit 2)
def ok : Result int str := Ok 42
```

For no-payload variants like `None`, the type parameter cannot be inferred from arguments alone — a type annotation (`: Option int`) provides the necessary constraint for the compiler to resolve `A = int`.

Variants with refinement-constrained payloads require proof obligations at construction time:

```ligare
def PosOption : prop := enum
  | Nothing
  | Just of (val : int where (x => x > 0))

def j : PosOption := Just 5       -- auto proof: 5 > 0
def k : PosOption := Just (-3)    -- compile error: -3 > 0 is false
```

### 10.3 Pattern Matching (Elimination)

Enum values are eliminated via `match` expressions.  Each branch covers one variant and binds its payload:

```ligare
def unwrap_or (opt : Option int) (default : int) : int :=
  match opt with
  | None     => default
  | Some val => val
```

**Theorem introduction** — every `match` branch automatically introduces a theorem that the scrutinee is of that variant, exactly like `if` branches introduce the condition theorem:

```ligare
match opt with
| None =>
  -- theorem: opt = None  (available in this branch)
| Some val =>
  -- theorem: opt = Some val  (available in this branch)
  -- if val has a refinement constraint (e.g. val > 0),
  -- that theorem is also available here
```

This enables safe refinement propagation through match branches:

```ligare
def safe_div (opt : PosOption) (x : int) : int :=
  match opt with
  | Nothing  => 0
  | Just val =>
    -- theorem: val > 0 (from PosOption's refinement)
    -- this satisfies div's proof obligation that the divisor is non-zero
    div x val
```

**Exhaustiveness checking** — the compiler verifies that every variant of the enum is covered.  Missing a variant is a compile-time error.

Nested matches are naturally supported:

```ligare
def eval (e : Expr) : int :=
  match e with
  | Lit n      => n
  | Add l r    => eval l + eval r
  | If c t e   => if eval c /= 0 then eval t else eval e
```

### 10.4 Erasure and Compilation

Enum **definitions** are `prop` — erased at compile time.  Enum **values** and `match` expressions are `data` — retained at runtime.

The C backend compiles enums to tagged union structs and `match` to `switch` statements, achieving zero-overhead representation:

```c
// Option_int (A = int)
typedef struct {
    int tag;          // 0 = None, 1 = Some
    union {
        struct { int64_t val; } Some;
    } data;
} Option_int;

// match opt with | None => 0 | Some val => val + 1
switch (opt.tag) {
case 0: return 0;
case 1: { int64_t val = opt.data.Some.val; return val + 1; }
}
```

### 10.5 Structs vs. Enums — Duality

| | Struct (product) | Enum (sum) |
|---|---|---|
| Logical dual | `∧` (all hold) | `∨` (one holds) |
| Construction | Provide all fields | Choose one variant |
| Elimination | Field projection (`.x`) | Pattern matching (`match`) |
| C representation | Contiguous fields | Tag + union |
| Universe | definition: `prop`, value: `data` | definition: `prop`, value: `data` |

## 11. Compile-Time Metaprogramming *(planned)*

The `proof` universe also serves the role of metaprogramming.
Any program used solely for generating `data` code can be written as a `proof` term, evaluated at compile time and spliced in.

**Planned mechanism**
```ligare
-- Quote: converts a code fragment into manipulable AST data
`( x + 1 )

-- Splice: inserts the AST produced by evaluating a proof term back into data context
$( proof_term )
```

**Safety guarantee**
During splicing, the generated code is forcibly verified to satisfy the target constraint; otherwise compilation fails.

Since `proof` is ultimately erased, the metaprogramming parts never enter the runtime.

## 12. Top-Level Commands

Ligare programs consist of a sequence of top-level commands:

| Command | Description |
|---------|-------------|
| `def <name> <params>? : <type>? := <body>` | Define a named term or function |
| `theorem <name> : <type> := <body>` | Define a named theorem (type-checked, then available as a term) |
| `#check <expr> : <type>` | Type-check an expression against a constraint |
| `#eval <expr>` | Evaluate an expression and display the result |

**Example program**  
```ligare
def nat := int where (x => x >= 0)
def x : nat := 10
theorem x_is_nat : nat := x by
  exact true

#check x : int
#eval x
```

## 13. Compilation and Erasure

The compilation process is divided into two major phases:

1. **Constraint checking and proof verification**  
   Perform constraint checking on all terms and verify that all `proof` obligations are satisfied.

2. **Erasure and code generation**  
   Retain all terms constrained by `data`, and remove all terms constrained by `prop`, `theorem`, or `proof`.  
   The final product is pure, zero-overhead executable code.

## 14. Summary

Ligare uses the single core concept of **"terms constrained by terms"** to unify:
- The type system (constraints as terms in `prop`)
- Propositions and proofs
- Design by contract (refinement types)
- Product types (structs) and sum types (enums) — both as constraints in `prop`
- Compile-time metaprogramming *(planned)*

It pursues **the extreme of static safety with zero runtime burden**, while maintaining a minimal set of concepts.  
This document describes the currently implemented syntax and planned features; formal definitions, operational semantics, and implementation details will be added progressively.
