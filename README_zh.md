# Ligare

> **一切皆项，一切皆约束。**  
> 文件后缀：`.lig`

[English version](README.md)

Ligare 是一个用 Rust 编写的实验性编程语言与编译器。它探索一个极简核心：值、类型、命题、证明、函数、数据声明和宏都表示为项，并由其他项约束。

当前仓库包含：

- 面向 `.lig` 源文件的词法器、解析器、类型检查器、求值器、格式化器和 C 后端。
- 基于 `ligare.toml` 的包模式，支持 new、build、update、test 和 fmt 命令。
- 对精化约束、证明块、结构体、和类型、模式匹配、模块、泛型和 C 代码生成的实验性支持。
- 位于 `crates/ligls` 的小型 `ligls` 语言服务器 crate。

Ligare 仍在活跃开发中。下方部分内容描述的是语言设计意图；明确标注为“计划中”的特性尚未实现。

## 快速开始

### 环境要求

- Rust 工具链。仓库包含 `rust-toolchain.toml`，使用 `rustup` 时会自动选择固定的工具链。
- 使用 `-o` 或包构建生成原生可执行文件时，需要系统中有可用的 `cc` C 编译器。

### 构建与测试

```bash
cargo build
cargo test
```

### 运行源文件

```bash
cargo run -- tests/fixtures/test.lig
cargo run -- tests/fixtures/test.lig --eval "1 + 2"
```

### 生成或编译 C

```bash
cargo run -- --emit-c tests/fixtures/test.lig
cargo run -- -o /tmp/ligare-test tests/fixtures/test.lig
```

### 构建包

```bash
cargo run -- new hello
cargo run -- build examples/test
./examples/test/target/test
```

### 格式化源码

```bash
cargo run -- fmt .
cargo run -- fmt --check .
```

## CLI 参考

```text
Usage: ligare [OPTIONS] [FILES]... [COMMAND]
```

| 命令或选项 | 描述 |
|------------|------|
| `ligare <files>` | 处理一个或多个 `.lig` 文件，并运行顶层检查/求值。 |
| `--eval <EXPR>` | 在处理输入文件后求值一个表达式。 |
| `--emit-c` | 输出 C 源码，而不是运行求值器。 |
| `-o, --output <PATH>` | 将生成的 C 编译为指定路径的原生可执行文件。 |
| `new [--bin\|--lib] PATH` | 创建新的包目录，包含 `ligare.toml` 和 `src` 入口文件。 |
| `build [PATH]` | 构建 `PATH` 或当前目录中的包。 |
| `update [NAME] [VERSION]` | 刷新 `ligare.lock`，也可以固定某个依赖版本。 |
| `test [PATH]` | 运行包中名称以 `_test.lig` 结尾的测试文件。 |
| `fmt [--check] [PATH]` | 格式化 `.lig` 文件，或检查是否需要格式化。 |

## 包清单

包构建使用 `ligare.toml`：

```toml
[package]
name = "test"
version = "0.1.0"
type = "binary"

[dependencies]
```

支持的包类型是 `binary` 和 `lib`。如果省略 `entry`，Ligare 会使用该包的默认源文件入口。依赖可以指向 Git 仓库或本地路径。

## 仓库结构

```text
src/front/        词法器与解析器
src/core/         核心项语法、arena 分配、求值、去糖化
src/checker/      约束检查、推导、证明搜索、擦除
src/compiler/     文件/模块流水线、项目加载、单态化
src/backend/      IR 与 C 代码生成
src/package/      manifest、lockfile 与依赖解析
crates/ligls/     实验性语言服务器 crate
tests/            集成与回归测试
tests/fixtures/   测试使用的 .lig 示例程序
examples/test/    Ligare 包示例
docs/             语法说明
```

## 1. 核心哲学

Ligare 是一种极简主义编程语言。它只承认一种实体——**项（Term）**。  
没有独立的"类型"语法，没有"类型与值"的二分，也没有"程序与证明"的二分。  
一切皆为项，一切关系皆为**约束**。

## 2. 项与约束

### 2.1 项
项是语言中唯一的存在。变量、字面量、函数、数据类型、命题、证明、宏……统统是项。

### 2.2 约束
项与项之间通过**约束**产生关系。  
`a : T` 表示项 `a` 受项 `T` 约束（即 `a` 的类型为 `T`）。  
约束关系取代了传统语言中的"类型归属"，但约束本身也是项，可以被其他项约束。

**示例**  
```ligare
3 : int       -- 3 受 int 约束
int : prop    -- int 受 data 约束
```

### 2.3 层级
所有项具有层级。约束关系强制层级有序，以防止罗素悖论式的自指结构。  
（具体层级规则将在形式化部分详细定义。）

### 2.4 命名规范
- **约束 / 类型**：大驼峰（如 `Nat`、`Point`、`LinkedList`）
- **函数 / 定理**：蛇形命名（如 `div`、`is_sorted`、`add_node`）

## 3. 元约束

语言内置四种根约束，称为**元约束**。它们定义了宇宙的根基。

| 元约束 | 含义 | 运行时存在？ |
|--------|------|--------------|
| `data` | 可计算的数据宇宙，一切最终保留的项皆归于此 | 是 |
| `prop` | 命题宇宙，描述逻辑条件 | 否（擦除） |
| `theorem` | 已成立的命题，封装证明 | 否（擦除） |
| `proof` | 证明的具体构造，是证据项 | 否（擦除） |

所有用户定义的约束最终都根植于这四个元约束之下。

## 4. 精化约束（Where 子句）

用户可以通过在已有约束上附加谓词来定义新约束。这是 Ligare 定义"子类型"的方式。

**语法**  
```ligare
def nat := int where (x => x >= 0)
```

**解读**  
`nat` 是一个新约束，任何受 `nat` 约束的项必须：
1. 受 `int` 约束（`int` 本身受 `data` 约束）；
2. 满足谓词 `x >= 0`。

**使用**  
```ligare
def x : nat := 10
#check x : nat       -- 通过
#check x : int       -- 也通过（nat 是 int 的子类型）
#check -5 : nat      -- 失败：-5 不 >= 0
```

编译器在需要处自动要求该证明，或通过上下文推导。

同一程序可定义多个精化约束：
```ligare
def pos   := int where (x => x > 0)
def even  := int where (x => x % 2 = 0)
def ten   := int where (x => x = 10)
```

精化约束也可内联用于函数参数：
```ligare
def sdiv (a : int) (b : int where (x => x /= 0)) : int := a / b
```

## 5. 函数

函数使用 `def`（或 `func`）定义，采用柯里化参数列表。通过 `where` 子句约束参数，形成前置条件契约。

**语法示例**  
```ligare
def div (a : int) (b : int where (x => x /= 0)) : int := a / b
```

**证明义务**  
- 调用方必须提供 `b /= 0` 的证明（或由编译器自动推导）。
- 函数体在参数约束成立的保证下执行。

所有证明项（`proof`）在编译期检查通过后擦除，不影响运行性能。

**无返回值类型标注的函数**  
```ligare
def id (x : int) := x
```

**递归函数**  
```ligare
def fib (n : int) : int :=
  if n < 2 then n else fib (n - 1) + fib (n - 2)
```

## 6. if 表达式与定理引入

`if` 的条件被视为一个命题。进入分支时，分支上下文会自动引入一个对应的 `theorem`。

**示例**  
```ligare
if x > 0 then
  -- 此处自动获得 theorem: x > 0
  -- 可用于满足其他约束的证明义务
  div 10 x  -- 此处 x /= 0 可由 x > 0 自动推导
else
  -- 此处自动获得 theorem: not (x > 0)
```

编译后，`if` 仍被编译为简单的条件跳转，证明部分全部擦除。

## 7. 证明与策略（Lean 4 风格 `by` 块）

Ligare 支持通过带策略的 `by` 块进行交互式证明构造，灵感来自 Lean 4。

**使用 `exact` 的简单证明**  
```ligare
#check 5 by
  exact true : nat
```

**使用 `intro` 的多策略证明**  
```ligare
#check 0 by
  intro
  exact 0 : int -> int
```

**独立的证明项（无主体）**  
```ligare
#check (by
  intro
  exact 0) : int -> int
```

**立即应用证明**  
```ligare
#eval (by
  intro
  exact 0) 5
```

可用策略：
- `exact <term>` — 直接提供满足目标的项
- `intro [name]` — 引入 Pi 类型的假设
- `apply <term>` — 应用函数以归约目标
- `have <name> := <term>` — 引入引理

## 8. 表达式与 Let 绑定

### Lambda 表达式
```ligare
-- 旧语法（仍然支持）
\x. x + 1
\a. \b. a + b

-- 新 `fun` 语法（推荐）
fun x => x + 1
fun x y => x + y
fun (x : int) => x + 1
fun a (b : int) => a + b
```

### Let 表达式
```ligare
let x := 5 in x + 3
let x : int := 5 in x
let x := 5 in let y := x + 1 in y * 2
```

### 类型标注
```ligare
(5 : int)
(5 : nat) by exact true
```

### 函数（Pi）类型
```ligare
int -> bool               -- 非依赖箭头
(x : int) -> x            -- 依赖箭头
```

### 命题组合子
```ligare
∧ P Q    -- 合取：P ∧ Q
∨ P Q    -- 析取：P ∨ Q
¬ P      -- 否定：¬P
```

## 9. 结构体

结构体**定义**是一个**约束**——存在于 `prop` 宇宙，类型检查后被擦除。结构体**值**（构造出的实例）存在于 `data` 宇宙，运行时保留。

结构体拥有命名字段。它是 Ligare 的**积类型**（∧）：所有字段同时存在。由于精化类型（`where` 子句）已经可以处理不变量，结构体专注于命名数据的组合。

**语法**
```ligare
def Point : prop := struct
  x : int
  y : int
```

**构造**
```ligare
def p : Point := Point.mk 3 4
```

**字段投影**
```ligare
#check Point.x p : int
def get_x (pt : Point) : int := Point.x pt
```

**工作原理**
- `Point.mk` 是自动生成的构造器，按顺序接受字段值。
- `Point.x` 是自动生成的投影器，从结构体值中提取命名字段。
- 编译器从结构体定义自动生成这些函数。
- 构造时验证字段约束。

**C 表示**
```c
typedef struct Point {
    int64_t x;
    int64_t y;
} Point;
```

## 10. 和类型

和类型**定义**是一个**约束**——存在于 `prop` 宇宙，类型检查后被擦除。和类型**值**（变体实例）存在于 `data` 宇宙，运行时保留。

和类型拥有命名变体，每个变体可附带零个或多个 payload 字段。它是 Ligare 的**和类型**（∨）：恰好一个变体成立。

### 10.1 定义

和类型使用与 `struct` 对称的 `enum` 关键字。每个变体以 `|` 引入：

```ligare
-- 简单枚举（无 payload）
def Color : prop := enum
  | Red
  | Green
  | Blue

-- 带 payload 的多态和类型
def Option (A : prop) : prop := enum
  | None
  | Some of (val : A)

-- 递归和类型 —— 编译器 AST 的核心
def Expr : prop := enum
  | Lit  of (n : int)
  | Add  of (l : Expr) (r : Expr)
  | If   of (c : Expr) (t : Expr) (e : Expr)

-- 多字段带名 payload
def Result (T : prop) (E : prop) : prop := enum
  | Ok  of (value : T)
  | Err of (error : E)
```

### 10.2 构造

变体名即为构造器函数，由 enum 定义自动生成：

```ligare
def c  : Color       := Red
def x  : Option int  := Some 5
def y  : Option int  := None              -- 需要类型标注来推断类型参数
def e  : Expr        := Add (Lit 1) (Lit 2)
def ok : Result int str := Ok 42
```

对于无参变体（如 `None`），类型参数无法从参数推导，需要类型标注（`: Option int`）为编译器提供推断 `A = int` 所需的约束信息。

带精化约束的 payload 在构造时需要证明义务：

```ligare
def PosOption : prop := enum
  | Nothing
  | Just of (val : int where (x => x > 0))

def j : PosOption := Just 5       -- 自动证明：5 > 0
def k : PosOption := Just (-3)    -- 编译错误：-3 > 0 不成立
```

### 10.3 模式匹配（消去）

和类型的值通过 `match` 表达式消去。每个分支覆盖一个变体，并绑定其 payload：

```ligare
def unwrap_or (opt : Option int) (default : int) : int :=
  match opt with
  | None     => default
  | Some val => val
```

**定理引入** —— 每个 `match` 分支自动引入该变体成立的 theorem，与 `if` 分支引入条件 theorem 完全一致：

```ligare
match opt with
| None =>
  -- 此处自动获得 theorem：opt = None
| Some val =>
  -- 此处自动获得 theorem：opt = Some val
  -- 如果 val 有精化约束（如 val > 0），该 theorem 同样可用
```

这使得精化约束能安全地穿透 match 分支：

```ligare
def safe_div (opt : PosOption) (x : int) : int :=
  match opt with
  | Nothing  => 0
  | Just val =>
    -- theorem：val > 0（来自 PosOption 的精化约束）
    -- 这满足了 div 对除数非零的证明义务
    div x val
```

**穷尽性检查** —— 编译器验证 match 覆盖了 enum 的所有变体。漏掉变体是编译期错误。

嵌套 match 自然支持：

```ligare
def eval (e : Expr) : int :=
  match e with
  | Lit n      => n
  | Add l r    => eval l + eval r
  | If c t e   => if eval c /= 0 then eval t else eval e
```

### 10.4 擦除与编译

和类型**定义**属于 `prop` —— 编译期擦除。和类型**值**和 `match` 表达式属于 `data` —— 运行时保留。

C 后端将 enum 定义编译为 tagged union 结构体，`match` 编译为 `switch` 语句，实现零开销表示：

```c
// Option_int（A = int）
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

### 10.5 结构体与和类型 —— 对偶性

| | 结构体（积） | 和类型（和） |
|---|---|---|
| 逻辑对偶 | `∧`（全部成立） | `∨`（择一成立） |
| 构造 | 提供所有字段 | 选择一个变体 |
| 消去 | 字段投影（`.x`） | 模式匹配（`match`） |
| C 表示 | 连续字段 | tag + union |
| 宇宙 | 定义：`prop`，值：`data` | 定义：`prop`，值：`data` |

## 11. 编译期元编程 *(计划中)*

`proof` 宇宙同时承担元编程的角色。
任何仅用于生成 `data` 代码的程序，都可以写成 `proof` 项，在编译期求值并拼接。

**预期机制**
```ligare
-- 引号（quote）：将代码片段转为可以操作的 AST 数据
`( x + 1 )

-- 拼接（splice）：将 proof 项执行得到的 AST 插回 data 上下文
$( proof_term )
```

**安全保证**
拼接时强制验证生成的代码满足目标约束，否则编译失败。

由于 `proof` 最终被擦除，元编程部分完全不会进入运行时。

## 12. 顶层命令

Ligare 程序由一系列顶层命令组成：

| 命令 | 描述 |
|------|------|
| `def <名称> <参数>? : <类型>? := <体>` | 定义命名项或函数 |
| `theorem <名称> : <类型> := <体>` | 定义命名定理（经类型检查后可作为项使用） |
| `#check <表达式> : <类型>` | 对表达式进行类型检查 |
| `#eval <表达式>` | 求值表达式并显示结果 |

**示例程序**  
```ligare
def nat := int where (x => x >= 0)
def x : nat := 10
theorem x_is_nat : nat := x by
  exact true

#check x : int
#eval x
```

## 13. 编译与擦除

编译过程分为两大阶段：

1. **约束检查与证明验证**  
   对所有项进行约束检查，验证所有 `proof` 义务是否满足。

2. **擦除与代码生成**  
   保留所有受 `data` 约束的项，删除所有受 `prop`、`theorem`、`proof` 约束的项。  
   最终产物是纯粹的、无运行开销的可执行代码。

## 14. 总结

Ligare 用 **"项约束项"** 这一个核心概念，统一了：
- 类型系统（约束是 `prop` 中的项）
- 命题与证明
- 契约式设计（精化类型）
- 积类型（struct）与和类型（enum）—— 两者皆作为 `prop` 中的约束
- 编译期元编程 *(计划中)*

它追求**静态安全的极致与运行时的零负担**，同时保持概念的极小集合。  
这份文档描述了目前已实现的语法与计划中的特性；形式化定义、操作语义及实现细节将逐步补充。
