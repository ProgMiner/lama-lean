# Lama Language Project Notes

> **Note:** This document reflects only the **current** state of the codebase. It contains facts not derivable from reading the Lean source alone (real Lama semantics, engine divergences, AST mapping decisions). It does **not** track history — no references to prior revisions, removed constructs, or past review findings. If a feature is absent from the code, it is absent from this document.

This project formalizes the Lama programming language (Lambda-Algol, v1.30) in Lean 4.
The official spec is at https://github.com/PLTools/Lama (branch `1.30`).
The authoritative source is both the LaTeX spec (`spec/*.tex`) AND the OCaml implementation (`src/Language.ml`) — they diverge in places.

## Project Goal

This project is intended for **reasoning about the semantics** of Lama programs — not for building a complete compiler. The Lean AST is a *semantic core* that deliberately diverges from the OCaml reference AST in several places. These divergences are intentional design choices that make the formalization more amenable to proof: they reduce representation ambiguity, expose semantically relevant distinctions as type-level differences, and omit features (user-defined operators, the full module/qualifier system, general intrinsics) that are irrelevant to the core dynamic semantics we aim to formalize.

## Project Structure

- `Lama/Ast/Ident.lean` — `Ident`, `Tag` (String-wrapper structures), `Binop` (closed 12-constructor enum for built-in operators)
- `Lama/Ast/Pattern.lean` — `Pattern` (12 constructors: wildcard, const, string, array, sexp, named, 6 type-tags)
- `Lama/Ast/Expr.lean` — Mutual `Expr`/`Scope`/`Definition` + `abbrev Program := Scope`
- `Lama/Ast.lean` — Umbrella module
- `Lama/Semantics/Eval.lean` — All semantic definitions: `Box`, `Error`, `RValue`, `EnvValue`, `SimpleEnv`, `BoxValue`, `Memory`, `Environment`, `EnvLookup`, `State`, `LValue`, `Value`, `Result`; the evaluation functions (`evalVar`, `checkRef`, `evalBinop`, `evalElem`, `evalElemRef`, `prepareCall`, `commitCall`, `evalAssignR`, `evalAssign`, `evalPattern`, `evalPatternList`, `chooseCaseR`, `chooseCase`, `prepareDefList`); and the `Eval`/`EvalList` inductive relations. Also defines the helper functions `Option.toExcept`, `List.set?`, `ByteArray.set?`
- `Lama/Semantics/Unique.lean` — `Eval_unique` theorem proving determinism of evaluation (complete, ~1077 lines, no sorries)
- `Lama/Semantics/Monotonic.lean` — `SameShape` relations on `EnvValue`/`BoxValue`/`SimpleEnv`/`Environment` (reflexive, symmetric, transitive); `Memory.LE` and `State.LE` orderings (monotonicity: `bound` grows, existing cells preserve shape, environment preserves shape); `Preorder Memory`/`Preorder State` instances; key theorems: `Environment.assign_memory_monotonic`, `Environment.assign_same_shape`, `BoxValue.assign_same_shape`, `evalVar_state_monotonic`, `evalAssign_state_monotonic`, `Eval_state_monotonic` (evaluation is monotonic: `Eval st e (.ok x st') → st ≤ st'`) (~624 lines, no sorries)
- `Lama/Semantics.lean` — Umbrella module, imports `Lama.Semantics.Eval`, `Lama.Semantics.Unique`, `Lama.Semantics.Monotonic`
- `Lama.lean` — Root, imports `Lama.Ast` and `Lama.Semantics`
- Toolchain: `leanprover/lean4:v4.28.0-rc1`, mathlib dependency
- Build: `lake build Lama` (plain `lake build` fails due to pre-existing target name mismatch)

## Known Spec vs Implementation Divergences

### `fun` vs `var x = fun ...`

| | `fun x (...) { ... }` | `var x = fun (...) { ... }` |
|---|---|---|
| Mutability | Immutable (`FVal`) — cannot reassign | Mutable (`Mut`) — can reassign |
| Recursion | Self-recursive and mutually recursive (all `fun` defs in scope are pre-bound via `FunRef` before body executes) | No mutual recursion (sequential init — initializer evaluated before later bindings exist) |
| Closure | Lazy: `FunRef` → `Closure` at first call time, captures `State.prune st level` | Eager: `Closure` created at definition time, captures `[|st|]` directly |

### Assignment semantics — two mechanisms

- **Variable assignment** (`Ref x := e`): In the interpreter, `State.update` does **functional** environment update (`bind x v s = fun y -> if x = y then v else s y`). No physical mutation. In the SM, `locals.(i) <- z` is physical mutation of an array slot. In x86-64, it's a `movq` into a stack offset.
- **Array/sexp/string element** (`ElemRef(x, i) := e`): **Always physical in-place mutation** — `a.(i) <- x` in all three engines.

### Scope exit destroys bindings

The interpreter uses `State.drop` to pop `L(scope, env, parent)` frames. After `Leave`, all variable bindings in that scope are gone. Closures hold **snapshots** (`State.prune`), not live references. The x86-64 compiler deallocates the stack frame on function return. There is **no dangling reference concept** — instead, accessing a variable whose scope has exited either fails at runtime (interpreter: `"name is undefined or does not designate a variable"`) or is impossible (compiled code: stack frame is gone).

### `:=` result by attribute mode

| `atr` | AST produced | Evaluates to |
|-------|-------------|-------------|
| `Val` | `Assign(Ref x, e)` | RHS value (normal case) |
| `Void` | `Ignore(Assign(Ref x, e))` | No value (popped from stack) |
| `Weak` | `Seq(Assign(Ref x, e), Const 0)` | 0 (default/bottom value ⊥) |
| `Reff` | `Assign(Ref x, e)` | RHS value, but it's an r-value — cannot be used as LHS |

The attribute system is applied during parsing; the SM compiler rejects non-Ref/non-ElemRef LHS for `:=`.

### Built-in binary operators (7 precedence levels, low→high)

| Level | Operators | Assoc | Semantics |
|-------|-----------|-------|-----------|
| 1 | `:=` | right | Assignment; cannot be redefined; LHS must be Ref |
| 2 | `:` | right | List cons |
| 3 | `!!` | left | Logical disjunction (nonzero=truth) |
| 4 | `&&` | left | Logical conjunction |
| 5 | `== != <= < >= >` | non-assoc | Integer comparisons (`=` alone is NOT equality) |
| 6 | `+ -` | left | Integer add/sub |
| 7 | `* / %` | left | Integer mul/quot/rem |

User-defined infix operators slot in by relative precedence (`at`/`before`/`after`).

### Operator semantics across engines

- **`&&` / `!!`**: **Strict** (no short-circuit) in all three engines — both operands evaluated before the operator applies.
- **`==` / `!=` on mixed types**: Diverges across engines.
  - Interpreter: structural inequality on mixed types (int/box compare unequal, never errors).
  - SM: returns `0` for int/box; **fails** for box/box (`failwith "unexpected operands"`).
  - x86-64: **traps** ("Comparing BOXED and UNBOXED value").
  - The Lean model uses `RValue` equality (int/int: value, box/box: address/identity, int/box: never equal), never errors. This matches the interpreter, not the compiled engines.
- **Division / modulo by zero**: Interpreter OCaml `/` raises `Division_by_zero`; compiled x86-64 `idivq` → SIGFPE; SM traps. The Lean model returns `Int.tdiv n 0 = 0` / `Int.tmod n 0 = 0`.
- **Division rounding**: Truncated division (`Int.tdiv` / `Int.tmod`) matches OCaml `(/)` / `(mod)` for all practical cases.

### Definition initialization order

All definitions in a scope are pre-processed before the body runs. `fun` definitions are all pre-bound (mutually recursive) before any initializer runs. `var` initializers run **sequentially in source order** before the body. In compiled Lama, every local is allocated and zero-initialized upfront (GC requirement); the compile-time environment covers the whole scope, so a `var a = b` where `b` is defined later loads `b`'s zeroed slot (no "undefined" error). The interpreter does not pre-allocate — forward references to later `var` bindings error.

### Control-flow result values

- `while` loop exit → `0` (⊥, per spec `Weak` rule `while e do s od; ⊥`).
- `skip` → `0` (⊥).

### I/O and effects omitted

The Lean semantics **intentionally omits** I/O and side-effect tracking. The AST has no I/O constructors, and the `Eval` relation carries no effect trace. In real Lama, `read` consumes an integer from the input stream and `write e` appends `e` to the output (compiled x86-64 returns `0`; spec `Weak`-forms it as `write(e); ⊥` with ⊥ ≡ `int 0`; the interpreter pushes `Value.Empty`). Modeling I/O would require threading an input/output state through `Eval`; this is deferred to avoid the complexity until needed for adequacy proofs over I/O behavior.

### Pattern variables mutability

Interpreter binds pattern variables as `Unmut` (immutable). SM/x86 compiler binds them as `Mut` (mutable). The Lean model uses mutable bindings (matches compiled).

### Closure capture and write-back

- `fun x(...){...}`: closure created lazily at first `Var x` access, capturing `State.prune st level` (snapshot of the defining scope chain, excluding caller's locals). Each access mints a **fresh** closure (interpreter: fresh `Closure`; compiled: fresh `CLOSURE`/`PROTO` object). Observable via `==`: `f == f` → `0` (distinct boxes) for `fun f`; `g == g` → `1` for `var g = f`.
- `var x = fun(...){...}`: closure created eagerly at definition time, capturing `[|st|]` (full current state, no prune).
- **Closure slot write-back**: The interpreter mutates `closure.(0) <- st''` after each call (coarse, whole-state write-back, visible to re-entrant calls of the same closure object). Compiled engines do per-slot immediate mutation (`ST (Access i)` / `closure.(i) <- z`). The Lean model does per-slot immediate mutation.
- **Compiled named-function call optimization**: A named function with no captured variables is called directly via label (`CALL f`) with no closure object created. The interpreter always creates one. Observable only by probing the value with `#fun` pattern — direct calls never materialize a closure value.

### `lamac` behavior (verified)

- **Duplicate names in one scope**: Rejected at compile time in all compiled modes (default x86-64, `-s`, `-b`, `-32`) for all 4 combinations (`var`+`var`, `fn`+`fn`, `var`+`fn`, `fn`+`var`). Error: `Error: name "X" is already defined in the scope`. The check is in `SM.ml` `check_name_and_add` (shared by all compiled backends), tests only the **name** (ignores kind), runs during compilation.
- **Only `lamac -i`** (source interpreter) tolerates duplicates and performs sequential assign (`{ var x = 1; var x = x + 10; x }` → `11` under `-i`).
- **Scope syntax**: In Lama ≥ 1.10, scope expressions use **round brackets `( ... )`**. `{ ... }` in expression position is a **list literal** (`listExpression : { [expr (, expr)*] }`), not a scope. A scope is `( definition* [expression] )` or a `fun` body `{ scopeExpression }`. Definitions are juxtaposed with **no separator**; `var` definitions consume their own mandatory `;` (part of the `var` production); `fun` definitions have **no terminator** (the closing `}` ends them). A trailing `;` after a `fun` definition is a parse error.

## Intentional Lean AST Design Divergences from the OCaml Reference

### Unified `call` (planned split into `funCall`/`closureCall`)

The OCaml AST has a single `Call of t * t list` where the callee is any expression. The current Lean AST also uses a single `call (x : Expr) (xs : List Expr)`. The planned design splits into:
- `funCall (fn : Ident) (args : List Expr)` — call to a named function
- `closureCall (fn : Expr) (args : List Expr)` — call to a closure / arbitrary expression

`Call(Var "f", args)` and `Call(Ref "f", args)` in the OCaml AST both map to `funCall "f" args` (both go through `FunRef` resolution). Arbitrary callee expressions map to `closureCall`. Named calls resolve via `FunRef` (pre-bound, self-recursive, lazy closure creation); closure calls evaluate the callee to a `Closure` value and enter it directly. Splitting at the type level makes this semantic distinction explicit.

### `Intrinsic` / `Control` omitted

The OCaml AST has `Intrinsic` and `Control` — higher-order functions from config to config, used for scheduling-based evaluation. The Lean AST omits both entirely. `Intrinsic`/`Control` are evaluation-scheduling mechanisms, not semantic constructs. Other intrinsics (`.elem`, `length`, `.array`, `string`) are covered by dedicated AST nodes (`elem`, `elemRef`, `arr`) or are irrelevant to core dynamic semantics. The I/O intrinsics (`read`, `write`) are also omitted (see "I/O and effects omitted" above).
### Closed `Binop` enum instead of string-based operators

The OCaml AST has `Binop of string * t * t`. The Lean AST uses a closed `Binop` inductive with 12 constructors. User-defined infix operators are a syntactic extensibility feature omitted from the core. If needed, `Binop` can be extended with `userDef (name : Ident)`.

### No globals

In Lama, global variables are handled distinctly from ordinary scope-local variables (they live in a separate global namespace with different lookup/update paths in all three engines). The Lean semantics **intentionally omits** the concept of global variables entirely — all bindings are treated as scope-local. This is a deliberate simplification to avoid modeling the global/local dispatch distinction.

### No `Qualifier` on definitions

The OCaml `decl` includes a `qualifier` (`Local | Public | Extern | PublicExtern`) controlling module visibility. The Lean `Definition` omits this — within a single compilation unit, all definitions are effectively `Local`.

### No `VarKind` (mutability annotation) on definitions

The OCaml implementation tracks `Unmut | Mut | FVal` per definition. The Lean `Definition` does not carry this: `Definition.fn` = `FVal`, `Definition.var` = `Mut`. The `Unmut`/`val` case (immutable non-recursive binding) is not yet modeled.

### `Definition.var` uses `Expr` (sentinel `.skip`) instead of `Option Expr`

In compiled Lama programs, every allocated variable is automatically zero-initialized (GC requirement) — there is no truly "uninitialized" state at runtime. The `.skip` sentinel (evaluates to ⊥ ≡ `int 0`) is more faithful than `Option Expr`, which would introduce a `None` vs `Some Unit` distinction that does not exist at the machine level.

### No `atr` field on `case`

The OCaml `Case` carries an attribute and a source location. The Lean `case` omits both — `case` always produces an r-value; `ref`/`elemRef` handle l-value positions directly.

### `ref` and `elemRef` included

The Lean AST models a **post-attribution core** — the result after reference inference. `ref` and `elemRef` are the only way to represent the LHS of `assign`.

### `Ignore`, `Leave`, `DoWhile` excluded

- `Ignore` — covered by `seq` (its `fst` is implicitly discarded)
- `Leave` — scope exit handled implicitly at the end of `Scope.body` evaluation
- `DoWhile` — desugars to `Seq(body, While(cond, body))`

## Error Classification

The `Error` inductive in `Lama/Semantics.lean` classifies runtime failures into 5 categories. The `Result` type carries `Error` in its `.err` constructor (`Result.err (err : Error)`); evaluation helpers (`evalVar`, `evalBinop`, `evalElem`, `evalElemRef`, `evalAssign`, `prepareCall`, `chooseCase`, etc.) return `Except Error α` to thread the error kind through monadic combinators. The `Option.toExcept` helper (`.none → .error e`, `.some x → .ok x`) bridges `Option`-returning primitives into the `Except Error` monad, tagging each `.none` with the appropriate `Error`. `Result.toExcept`/`ofExcept` convert between `Result V` and `Except Error (V × State)`.

### Error categories

| Constructor | Meaning | Triggered by |
|---|---|---|
| `.metatheory` | Internal invariant violation — an impossible state that should never arise in a well-formed evaluation. Indicates a bug in the metatheory/model, not a user-facing runtime error. | `Environment.pop` returning `.none` in `Result.popEnv` (trying to pop a non-`scope` frame after `case`/`scope` body evaluation — `pop` returns `.none` for `empty`/`closure`); malformed closure box in `Environment.lookup`/`assign` (Environment is `closure b` but `mem b` is not `.closure`) and in `Environment.close` (`evalVar`, `lambdaErr`) — these can only arise from a bug in the metatheory, since `closure b` environments are constructed only in `prepareCall` after verifying `mem b = .closure …`, and normal evaluation never overwrites a closure box with a non-closure value. |
| `.name` | Name resolution failure — a variable name is either not found in the environment, or designates a function (not a variable). Matches the interpreter's `"name is undefined or does not designate a variable"`. | `Environment.lookup empty`, `Environment.lookup`/`assign` name-not-found-in-closure-scope, `Environment.assign` on a function binding (`.some (.fn _ _) => .error .name`), `checkRef` when the name denotes a function. |
| `.lvalue` | L-value / R-value category mismatch — an l-value appears where an r-value is expected. Also covers escaping local l-values (a `ref x` that survives the scope where `x` is bound — see "Escaping local l-values" in Model Adequacy Limits). | `Value.toRValue?` returning `.none` (in `evalBinop` `.eq`/`.ne`, `evalElem`, `evalElemRef`, `evalAssign` RHS, `chooseCase` scrutinee), `EvalList.err` (l-value in expression list), `Result.popEnv` escaping-local check (`x ∈ xs`), `commitCall` when function body returns an l-value. |
| `.type` | Structural type mismatch — a value of the wrong `RValue`/`BoxValue` variant for the operation. Not a static type error (the model has no static type system), but a runtime "wrong kind of value" error. | `RValue.toInt?` on a `.box` (via `toExcept .type` in `RValue.toNat?`, `Value.toInt?`, `Value.toBool?`), `Value.toBox?` on an `.int`, indexing a `.closure` (`evalElem`, `evalElemRefR`, `BoxValue.assign`), calling a non-closure (`prepareCall`), too few call arguments (`prepareCall` arity check). |
| `.runtime` | Runtime resource error — index out of bounds, negative index, or pattern-match failure. The operation is type-correct but fails due to runtime conditions. | `List.set?`/`ByteArray.set?` out of bounds (`BoxValue.assign`), `xs[y]?` out of bounds (`evalElem`, `evalElemRefR` bounds checks), negative integer to `Nat` (`RValue.toNat?`: `x.toNat?.toExcept .runtime`), no pattern matches in `case` (`chooseCase`). |

### Error propagation in `Eval`/`EvalList`

Error rules in the `Eval` inductive carry the error kind as a parameter (`varErr st x e`, `binopErr ... e`, `callErr₃ ... e`, etc.), preserving the classification through the derivation tree. Left-operand errors propagate the same error kind (`binopErrL ... e`, `assignErrL ... e`, etc.). Right-operand errors also propagate (`binopErrR ... e`, `loopErrR ... e`, etc.). `EvalList.err` hardcodes `.lvalue` for the l-value-in-list case; `errL`/`errR` propagate the error kind from the sub-evaluation.

### Notes on specific classifications

1. **`chooseCase` no-match → `.runtime`** (line 520): The code comment `-- or .type ???` marks an open question retained for future revisit if a static type system can recognize pattern-match exhaustiveness. `.runtime` is the correct classification under the current type-erased model — a non-exhaustive `case` (no pattern matches the scrutinee at runtime) is a runtime error, not a type error: the scrutinee's value kind is irrelevant; it simply doesn't match any pattern.

2. **`prepareCall` too-few-arguments → `.type`** (line 406): Calling a closure with fewer arguments than parameters is classified as a structural type mismatch. This is defensible (arity as a structural property), but `.runtime` would also be reasonable (arity mismatch as a runtime contract violation). The current `.type` choice is a judgment call.

## Model Adequacy Limits

Where the Lean model diverges from compiled Lama semantics, the direction of soundness:

- **`==`/`!=` on mixed types**: Model never errors; compiled x86-64 traps, SM fails on box/box. Sound over-approximation (never errors where compiled succeeds). Adequacy (`Eval … .ok ⇒ compiled yields same`) holds only for programs that never compare a box to an int/box at runtime.
- **Division by zero**: Model returns 0; compiled traps (SIGFPE). Intentional simplification to avoid modeling hardware traps.
- **Escaping local l-values via `Result.popEnv`**: If a `case`/`scope` returns `ref x` where `x` is a popped local binding, the model produces `.err`. The interpreter also errors (`State.drop` → lookup fails). Compiled SM/x86 **do not** — the stack frame persists, escaped references silently succeed. The model is **stricter** than compiled. Adequacy is one-directional: `Eval … .ok ⇒ compiled ok` holds; `Eval … .err ⇒ compiled errors` does **not** hold for this case. Faithful modeling would require `LValue.slot (b : Box)` instead of name-based l-values.
- **`assign` always returns RHS (`atr = Val`)**: The Lean AST has no `atr` field. `Void`/`Weak` modes must be desugared to `Ignore(assign)` / `Seq(assign, int 0)` at the AST level by a front-end before reaching the core. This desugaring is not implemented in-repo. `Weak` is representable via `seqOk`; `Void` would need an `Ignore` node (excluded — covered by `seq` discarding `fst`).
- **Closure slot write-back timing**: Model does per-slot immediate mutation (matches compiled). Interpreter does coarse `closure.(0) <- st''` write-back after call. Observable difference in re-entrant calls: model = compiled ≠ interpreter.
- **GC / allocation-order sensitivity**: Model memory is never reused (`bound` grows monotonically). Real Lama's GC may move objects. Combined with address-observing `==`, box-identity results are meaningful only up to allocation-order agreement.
- **`callOk` evaluation order assumption**: Model evaluates callee → args → body, matching "closure pushed below its arguments for `CALLC`". If the SM emits argument code before callee code, state threading diverges when both have state-dependent side effects like allocation. Not yet confirmed against `SM.ml`.

## Lean Technical Notes

- `DecidableEq` cannot be auto-derived for `Pattern` or the mutual `Expr`/`Scope`/`Definition` block (Lean limitation with nested inductives through `List`/`Option`/`×`)
- The auto-generated induction principle for the mutual block is weak for nested positions; future semantics code will need well-founded recursion or a custom eliminator
- `Inhabited` derives fine on the mutual block (derives from `Expr.skip`)
