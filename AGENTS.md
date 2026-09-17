# Lama Language Project Notes

> **Note:** This document reflects only the **current** state of the codebase. It contains facts not derivable from reading the Lean source alone (real Lama semantics, engine divergences, AST mapping decisions). It does **not** track history — no references to prior revisions, removed constructs, or past review findings. If a feature is absent from the code, it is absent from this document.

This project formalizes the Lama programming language (Lambda-Algol, v1.30) in Lean 4.
The official spec is at https://github.com/PLTools/Lama (branch `1.30`).
The authoritative source is both the LaTeX spec (`spec/*.tex`) AND the OCaml implementation (`src/Language.ml`) — both live in the upstream repo (not checked out here), and they diverge in places.

## Project Goal

This project is intended for **reasoning about the semantics** of Lama programs — not for building a complete compiler. The Lean AST is a *semantic core* that diverges from the OCaml reference AST in several places, as deliberate design choices that make the formalization more amenable to proof: they reduce representation ambiguity, expose semantically relevant distinctions as type-level differences, and omit features (user-defined operators, the full module/qualifier system, general intrinsics) that are irrelevant to the core dynamic semantics.

## Project Structure

- `Lama/Ast/Ident.lean` — `Ident`, `Tag` (String-wrapper structures), `Binop` (closed enum for the built-in operators, 13 constructors)
- `Lama/Ast/Pattern.lean` — `Pattern` (pattern language incl. 6 value-type tags)
- `Lama/Ast/Expr.lean` — Mutual `Expr`/`Scope`/`Definition` + `abbrev Program := Scope`
- `Lama/Ast/Closed.lean` — Static closedness predicates: `Context` (lexical context, a `Finmap` from `Ident` to `Bool`; `true` = variable binding, `false` = function definition) and the mutual `Expr.IsClosed`/`IsClosedList`/`IsClosedBranches` + `Definition.IsClosed`/`IsClosedList` predicates — an expression is closed when every referenced name is bound in the context; `.ref x` additionally requires a **variable** binding
- `Lama/Ast/WellFormed.lean` — Static value-category well-formedness: `Category` (`val` | `ref (xs : Finset Ident)`, the two-constructor collapse of the spec's `Ref | Val | Void | Weak` attribute system; `.ref` carries the payload of variable names the position's result may denote) and the mutual inductive judgment `Expr.WF : Expr → Category → Prop` (bottom-up category inference), with proven uniqueness (`Expr.WF_unique`), executable category inference (`Expr.inferCategory`), and `Definition.WF` (definition only; the `WF ⇒ no .lvalue error` capstone is future work)
- `Lama/Ast.lean` — Umbrella module
- `Lama/Semantics.lean` — Semantics umbrella module
- `Lama/Semantics/Eval.lean` — All semantic definitions: the runtime value types, the step-level evaluation helpers, and the `Eval`/`EvalList` inductive relations. `prepareDefList`'s duplicate-`var` handling is load-bearing for closedness soundness (see Closedness Invariant)
- `Lama/Semantics/Unique.lean` — `Eval_unique` proving determinism of evaluation
- `Lama/Semantics/Monotonic.lean` — `SameShape` relations on the environment/box types (reflexive, symmetric, transitive); `BoxValue.SameShape` is structural (compares sizes for `str`/`arr`, tags and lengths for `sexp`, `ClosedEnv.SameShape` for `closure`); `Memory.LE` and `State.LE` orderings (monotonicity: `bound` grows, existing cells preserve shape, environment preserves shape); `Preorder` instances; capstones `Eval_state_monotonic` and `EvalList_state_monotonic` (evaluation is monotonic: `Eval st e (.ok x st') → st ≤ st'`). Defines the generic `Except.SameShape` relational lifting combinator
- `Lama/Semantics/WellFormed.lean` — Runtime well-formedness invariant: per-type WF predicates for every semantic type, including `ClosedEnv.WF`; `Memory.WF` is a structure with two fields: `bound` (prefix-defined — cell `b` is undefined iff `¬ b.WF mem`) and `mem` (every cell's content is WF). `State.WF` is a structure with `env`/`mem` fields. Transport theorems move WF along the `Memory.LE`/`State.LE` preorder. Preservation theorems for every step-level operation; capstones `Eval_result_wf` and `EvalList_result_wf` (a well-formed state evaluates to a well-formed result)
- `Lama/Semantics/Error/Metatheory.lean` — Soundness proof: `.metatheory` errors never arise during well-formed evaluation (capstone `Eval_no_metatheory_error`). Key lemmas include `Environment.lookup_metatheory_error`, `Environment.close_none`, `Environment.assign_metatheory_error`, `evalVar_metatheory_error`, `checkRef_some_metatheory`, `evalElem_metatheory_error`, `evalAssign_metatheory_error`
- `Lama/Semantics/Closed.lean` — Soundness of the closedness condition, runtime side. Extends the static `IsClosed` predicates to runtime data: per-type `IsClosed` predicates (a closure's captured environment and body must be closed; a state is closed when its memory cells and environment chain are), plus `X.context` derivations (SimpleEnv/ClosedEnv/Environment/State project a runtime `Context` mirroring the static one — names mapped to `isVar`: bound-as-var vs bound-as-fn). Transport theorems move `IsClosed`/`context` along `SameShape` and the `Memory.LE`/`State.LE` preorder (`State.context_transport`: the context is invariant under evaluation — the key bridge for propagating closedness across sub-evaluations). Preservation for every step-level operation, incl. `prepareDefList_env_context` (`ctx.addDefs ds = xs.context ∪ ctx`); capstones `Eval_state_closed` and `EvalList_state_closed`. Also extends `Finmap` with a `map` operation and its simp lemmas
- `Lama/Semantics/Error/Name.lean` — Soundness proof: `.name` errors never arise in well-formed **closed** evaluation (capstone `Eval_no_name_error`). Key lemmas include `evalVar_name_error` (`evalVar st x = .error .name → x ∉ st.context`), `checkRef_some_name` (`checkRef st x = .some .name → st.context.lookup x ≠ .some true`), and `_no_name_error` lemmas for the step-level operations
- `Lama.lean` — Root umbrella importing `Lama.Ast` + `Lama.Semantics`
- Toolchain: `leanprover/lean4:v4.28.0-rc1`, mathlib dependency
- Build: `lake build Lama` (plain `lake build` fails due to pre-existing target name mismatch: `defaultTargets = ["lama"]` in `lakefile.toml` points at a commented-out `lean_exe` stub; the only real target is the `Lama` lean_lib. CI runs `leanprover/lean-action` whose auto-configured `lake build` hits the same mismatch)

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

In the model, function return mirrors this split: `commitCall` restores the **caller's** environment (as of after argument evaluation) while the **callee's final memory persists** — allocations outlive the call, environment frames do not.

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
| 5 | `== != <= < >= >` | non-assoc | Integer comparisons. Bare `=` is a *different* operator: in expression position it desugars to `compare x y == 0` (structural equality), besides its role as definition/pattern binding syntax |
| 6 | `+ -` | left | Integer add/sub |
| 7 | `* / %` | left | Integer mul/quot/rem |

User-defined infix operators slot in by relative precedence (`at`/`before`/`after`).

### Operator semantics across engines

- **`&&` / `!!`**: **Strict** (no short-circuit) in all three engines — both operands evaluated before the operator applies.
- **`==` / `!=` on mixed types**: Diverges across engines.
  - Interpreter: raises `Failure "int value expected"` — the generic `Binop` case applies `Value.to_int` to both operands before the operator, so **any** non-`Int` operand of any binop fails.
  - SM: returns `0` for int/box; **fails** for box/box (`failwith "unexpected operands"`).
  - x86-64: a runtime trap function exists ("Comparing BOXED and UNBOXED value"), but branch 1.30 emits no jump to it — comparisons compile to a bare `cmpq`, so the trap appears to be dead code.
  - The Lean model uses `RValue` equality (int/int: value, box/box: address/identity, int/box: never equal), never errors. This is a **deliberate over-approximation**: it matches none of the engines exactly (it is closest to the SM's int/box → 0 rule, but SM still fails on box/box).
- **Division / modulo by zero**: Interpreter OCaml `/` raises `Division_by_zero`; compiled x86-64 `idivq` → SIGFPE; SM traps. The Lean model returns `Int.tdiv n 0 = 0` / `Int.tmod n 0 = n` (rem-by-zero yields the dividend).
- **Division rounding**: Truncated division (`Int.tdiv` / `Int.tmod`) matches OCaml `(/)` / `(mod)` for all practical cases.

### Definition initialization order

All definitions in a scope are pre-processed before the body runs. `fun` definitions are all pre-bound (mutually recursive) before any initializer runs. `var` initializers run **sequentially in source order** before the body. In compiled Lama, every local is allocated and zero-initialized upfront (GC requirement); the compile-time environment covers the whole scope, so a `var a = b` where `b` is defined later loads `b`'s zeroed slot (no "undefined" error). The interpreter does not pre-allocate — forward references to later `var` bindings error.

### Control-flow result values

- `while` loop exit → `0` (⊥, per spec `Weak` rule `while e do s od; ⊥`).
- `skip` → `0` (⊥).

### I/O and effects omitted

The Lean semantics **intentionally omits** I/O and side-effect tracking. The AST has no I/O constructors, and the `Eval` relation carries no effect trace. In real Lama, `read` consumes an integer from the input stream and `write e` appends `e` to the output (compiled x86-64 returns `0`; spec `Weak`-forms it as `write(e); ⊥` with ⊥ ≡ `int 0`; the interpreter pushes `Value.Empty`).

### Pattern variables mutability

Interpreter binds pattern variables as `Unmut` (immutable). SM/x86 compiler binds them as `Mut` (mutable). The Lean model uses mutable bindings (matches compiled). On duplicate names within one pattern list, the **later** binder wins (`evalPatternList` unions left-biased, `env₂ ∪ env₁`).

### Closure capture and write-back

- `fun x(...){...}`: closure created lazily at first `Var x` access. `Environment.lookup`'s scope case calls `Environment.close st.mem` to snapshot the live `Environment` into a `ClosedEnv` (a hierarchical `empty | scope xs parent` structure preserving the scope chain); `evalVar` then allocates a `BoxValue.closure` box holding that `ClosedEnv`. Each access mints a **fresh** closure (interpreter: fresh `Closure`; compiled: fresh `CLOSURE`/`PROTO` object). Observable via `==`: `f == f` → `0` (distinct boxes) for `fun f`; `g == g` → `1` for `var g = f`.
- `var x = fun(...){...}`: closure created eagerly at definition time, capturing `[|st|]` (full current state, no prune). In the model, this is represented by the `lambda` expression evaluating in-place (its `Eval.lambdaOk` rule calls `close` at evaluation time, producing the snapshot `ClosedEnv`).
- **Closure environment representation**: The `ClosedEnv` stored in `BoxValue.closure` is a **hierarchical snapshot** (`scope xs parent`) preserving scope boundaries: `ClosedEnv.lookup`/`assign` walk the chain innermost-first, so shadowed variables are resolved and updated at the correct scope level. `EnvLookup.fn` carries the `ClosedEnv` snapshot, so a function value is self-contained.
- **Closure slot write-back**: The interpreter mutates `closure.(0) <- st''` after each call (coarse, whole-state write-back, visible to re-entrant calls of the same closure object). Compiled engines do per-slot immediate mutation (`ST (Access i)` / `closure.(i) <- z`). The Lean model does per-slot immediate mutation via `Environment.assign` on the `closure b` environment, which delegates to `ClosedEnv.assign` (walks the captured scope chain, updates the innermost matching `.var` binding, writes back via `Memory.assign b (.closure xs' params body)`).
- **Compiled named-function call optimization**: A named function with no captured variables is called directly via label (`CALL f`) with no closure object created. The interpreter always creates one. Observable only by probing the value with `#fun` pattern — direct calls never materialize a closure value.

### `lamac` behavior

- **Duplicate names in one scope**: Rejected at compile time in all compiled modes (default x86-64, `-s`, `-b`, `-32`) for all 4 combinations (`var`+`var`, `fn`+`fn`, `var`+`fn`, `fn`+`var`). Error: `Error: name "X" is already defined in the scope`. The check is in `SM.ml` `check_name_and_add` (shared by all compiled backends), tests only the **name** (ignores kind), runs during compilation.
- **Only `lamac -i`** (source interpreter) tolerates duplicates and performs sequential assign (`{ var x = 1; var x = x + 10; x }` → `11` under `-i`).
- **Scope syntax**: In Lama ≥ 1.10, scope expressions use **round brackets `( ... )`**. `{ ... }` in expression position is a **list literal** (`listExpression : { [expr (, expr)*] }`), not a scope. A scope is `( definition* [expression] )` or a `fun` body `{ scopeExpression }`. Definitions are juxtaposed with **no separator**; `var` definitions consume their own mandatory `;` (part of the `var` production); `fun` definitions have **no terminator** (the closing `}` ends them). A trailing `;` after a `fun` definition is a parse error.

## Intentional Lean AST Design Divergences from the OCaml Reference

### `Intrinsic` / `Control` omitted

The OCaml AST has `Intrinsic` and `Control` — higher-order functions from config to config, used for scheduling-based evaluation. The Lean AST omits both entirely. `Intrinsic`/`Control` are evaluation-scheduling mechanisms, not semantic constructs. Other intrinsics (`.elem`, `length`, `.array`, `string`) are covered by dedicated AST nodes (`elem`, `elemRef`, `arr`) or are irrelevant to core dynamic semantics. The I/O intrinsics (`read`, `write`) are also omitted (see "I/O and effects omitted" above).
### Closed `Binop` enum instead of string-based operators

The OCaml AST has `Binop of string * t * t`. The Lean AST uses a closed `Binop` inductive with 13 constructors. User-defined infix operators are a syntactic extensibility feature omitted from the core. Note that the spec's list-cons operator `:` (precedence level 2) is **not** among the constructors and has no other AST node — list-by-cons is not modeled in the core.

### No globals

In Lama, global variables are handled distinctly from ordinary scope-local variables (they live in a separate global namespace with different lookup/update paths in all three engines). The Lean semantics omits the concept of global variables entirely — all bindings are treated as scope-local — to avoid modeling the global/local dispatch distinction.

### No `Qualifier` on definitions

The OCaml `decl` includes a `qualifier` (`Local | Public | Extern | PublicExtern`) controlling module visibility. The Lean `Definition` omits this — within a single compilation unit, all definitions are effectively `Local`.

### No `VarKind` (mutability annotation) on definitions

The OCaml implementation tracks `Unmut | Mut | FVal` per definition. The Lean `Definition` does not carry this: `Definition.fn` = `FVal`, `Definition.var` = `Mut`. The `Unmut`/`val` case (immutable non-recursive binding) is absent from the model.

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

The `Error` inductive in `Lama/Semantics/Eval.lean` classifies runtime failures into 5 categories. The `Result` type carries `Error` in its `.err` constructor; evaluation helpers return `Except Error α` to thread the error kind through monadic combinators, with `Option.toExcept`/`Result.toExcept`/`ofExcept` bridging between the `Option`/`Result`/`Except` representations.

### Error categories

| Constructor | Meaning | Triggered by |
|---|---|---|
| `.metatheory` | Internal invariant violation — an impossible state that should never arise in a well-formed evaluation. Indicates a bug in the metatheory/model, not a user-facing runtime error. | `Environment.pop` returning `.none` in `Result.popEnv` (trying to pop a non-`scope` frame after `case`/`scope` body evaluation — `pop` returns `.none` for `empty`/`closure`; unreachable through `Eval` since a `case`/`scope` body always evaluates inside a pushed `scope` frame); malformed closure box in `Environment.lookup`/`assign` (Environment is `closure b` but `mem b` is not `.closure`) and in `Environment.close` (called from `Environment.lookup` scope case and `lambdaErr`) — these can only arise from a bug in the metatheory, since `closure b` environments are constructed only in `prepareCall` after verifying `mem b = .closure …`, and normal evaluation never overwrites a closure box with a non-closure value. `ClosedEnv.assign` returning `.none` (variable not found in the captured chain, or found as a `.fn` binding) in `Environment.assign` `closure` case — same root cause: a malformed closure environment; `Environment.assign` `scope` case on a `.fn` binding (assigning to a function name in a live scope) — unreachable through `Eval` since `.lvalue (.var x)` is only ever minted by `refOk` after `checkRef` confirmed the name designates a variable. Assigning to an undefined memory cell (`BoxValue.assign` on `.undefined`), indexing an undefined cell (`evalElem`), or assigning into an `empty` environment (`Environment.assign`) — all presuppose a state violating the WF invariant. `Environment.lookup` `scope` case calling `Environment.close` which returns `.none` (malformed closure box somewhere in the parent chain) — proven impossible in well-formed states by `Environment.close_none`. |
| `.name` | Name resolution failure — a variable name is either not found in the environment, or designates a function (not a variable). Matches the interpreter's `"name is undefined or does not designate a variable"`. | `Environment.lookup` on `empty` or a name missing from the closure scope; `checkRef` when the name denotes a function. |
| `.lvalue` | L-value / R-value category mismatch — an l-value appears where an r-value is expected. Also covers escaping local l-values (a `ref x` that survives the scope where `x` is bound — see "Escaping local l-values" in Model Adequacy Limits). | `Value.toRValue?` returning `.none` (in `evalBinop` `.eq`/`.ne`, `evalElem`, `evalElemRef`, `evalAssign` RHS, `chooseCase` scrutinee), `EvalList.err` (l-value in expression list), `Result.popEnv` escaping-local check (`x ∈ xs`), `commitCall` when function body returns an l-value. |
| `.type` | Structural type mismatch — a value of the wrong `RValue`/`BoxValue` variant for the operation. Not a static type error (the model has no static type system), but a runtime "wrong kind of value" error. | `RValue.toInt?` on a `.box` (via `toExcept .type` in `RValue.toNat?`, `Value.toInt?`, `Value.toBool?`), `Value.toBox?`/`RValue.toBox?` on an `.int` (`evalElem`, `evalElemRef`, `prepareCall`), indexing a `.closure` (`evalElem`, `BoxValue.assign`), calling a non-closure (`prepareCall`), too few call arguments (`prepareCall` arity check). |
| `.runtime` | Runtime resource error — index out of bounds, negative index, or pattern-match failure. The operation is type-correct but fails due to runtime conditions. | `List.set?`/`ByteArray.set?` out of bounds (`BoxValue.assign`), `xs[y]?` out of bounds (`evalElem` bounds checks), negative integer to `Nat` (`RValue.toNat?`: `x.toNat?.toExcept .runtime`, used by `evalElemRef` index and `BoxValue.assign` on `.str`), no pattern matches in `case` (`chooseCase`). |

### Error propagation in `Eval`/`EvalList`

Error rules in the `Eval`/`EvalList` inductives carry the error kind as a parameter, preserving the classification through the derivation tree: sub-evaluation errors propagate the same kind (left and right operands alike), `EvalList.err` hardcodes `.lvalue` for the l-value-in-list case.

### Notes on specific classifications

1. **`chooseCase` no-match → `.runtime`**: An open question marked in the source (`-- or .type ???`). `.runtime` is the correct classification under the current type-erased model — a non-exhaustive `case` (no pattern matches the scrutinee at runtime) is a runtime error, not a type error: the scrutinee's value kind is irrelevant; it simply doesn't match any pattern.

2. **`prepareCall` too-few-arguments → `.type`**: Calling a closure with fewer arguments than parameters is classified as a structural type mismatch (arity as a structural property); `.runtime` (arity mismatch as a runtime contract violation) would be an equally defensible choice. Surplus arguments are silently discarded — `prepareCall` zips params with args, so only too-few errors.

## Model Adequacy Limits

Where the Lean model diverges from compiled Lama semantics, the direction of soundness:

- **`==`/`!=` on mixed types**: Model never errors where compiled engines fail or trap (see "Operator semantics across engines"). Sound over-approximation. Adequacy (`Eval … .ok ⇒ compiled yields same`) holds only for programs that never compare a box to an int/box at runtime.
- **Division by zero**: Model returns 0; compiled traps (SIGFPE). Intentional simplification to avoid modeling hardware traps.
- **Escaping local l-values via `Result.popEnv`**: If a `case`/`scope` returns `ref x` where `x` is a popped local binding, the model produces `.err`. The interpreter also errors (`State.drop` → lookup fails). Compiled SM/x86 **do not** — the stack frame persists, escaped references silently succeed. The model is **stricter** than compiled. Adequacy is one-directional: `Eval … .ok ⇒ compiled ok` holds; `Eval … .err ⇒ compiled errors` does **not** hold for this case. L-values are name-based (`LValue.var (x : Ident)`) by deliberate design choice. The strictness matches the interpreter, the spec's reference engine, so the asymmetry is a compiled-engines infidelity, not a model defect; the static side mirrors it with the `Disjoint` premises of the `caseRef`/`scopeRef` constructors of `Ast/WellFormed.lean`.
- **`assign` always returns RHS (`atr = Val`)**: The Lean AST has no `atr` field, so `Void`/`Weak` modes must be desugared at the AST level by a front-end before reaching the core. This desugaring is not implemented in-repo; `Weak` is representable via `seqOk`, but `Void` would need an `Ignore` node (excluded — covered by `seq` discarding `fst`).
- **Duplicate names in one scope**: Compiled Lama rejects duplicates at compile time, so no compiled program is affected (the model's divergence from `lamac -i`'s sequential-assign semantics is described under "`lamac` behavior"; the model's own last-definition-wins rule and its soundness role are described under "Closedness Invariant"). Divergence is observable only when a later initializer references the duplicated name.
- **Closure slot write-back timing**: Observable difference in re-entrant calls: model = compiled ≠ interpreter (see "Closure capture and write-back").
- **GC / allocation-order sensitivity**: Model memory is never reused (`bound` grows monotonically). Real Lama's GC may move objects. Combined with address-observing `==`, box-identity results are meaningful only up to allocation-order agreement.
- **`callOk` evaluation order**: Model evaluates callee → args → body. Verified against the upstream engines: `SM.ml` compiles `Expr.Call` with `compile_list … (f :: args)` (callee code before argument code), and at runtime `CALLC` splits the stack with the closure below its arguments — so a callee evaluated first sits deeper. Confirmed behaviorally in all engines (interpreter, SM, x86-64, x86-32) with a side-effecting callee expression: effects run callee-first everywhere.

## Well-Formedness Invariant

The `WellFormed.lean` module formalizes a **runtime well-formedness invariant** that characterizes states where the heap and environment are structurally consistent. This invariant is the key prerequisite for proving that `.metatheory` errors never occur during well-formed evaluation.

### Memory well-formedness (`Memory.WF`)

`Memory.WF` is a `structure` with two propositional fields:

- `bound` — the memory is **prefix-defined**: cell `b` is undefined (`mem.mem b = .undefined`) if and only if `¬ b.WF mem` (equivalently, `mem.bound ≤ b.cell`). All and only the cells below the high-water mark are defined. This rules out "holes" inside the allocated region.
- `mem` — every defined cell's content is itself well-formed (`(mem.mem b).WF mem`).

A companion `Memory.WF_iff` lemma converts between the structure form and a conjunction for rewriting. The prefix-defined invariant is the machine-level property that makes monotonicity and shape arguments sound.

### Environment well-formedness (`Environment.WF`)

`Environment.WF mem env` is a structural predicate:

- `.empty` → trivially well-formed.
- `.closure box` → the box must actually hold a closure value in memory (`∃ env params body, mem.mem box = .closure env params body`). This closes the loop between environment structure and heap contents, ruling out the "malformed closure box" `.metatheory` errors from `Eval.lean`.
- `.scope _ env` → the tail environment must be well-formed.

`Environment.WF` is marked `[reducible, simp]` so `simp` can unfold it automatically.

### ClosedEnv well-formedness (`ClosedEnv.WF`)

`ClosedEnv.WF mem env` is a `[reducible, simp]` structural predicate:

- `.empty` → trivially well-formed.
- `.scope xs env` → `xs.WF mem ∧ ClosedEnv.WF mem env` (both the current scope's bindings and the parent chain must be well-formed).

This ensures every `ClosedEnv` snapshot stored in a `BoxValue.closure` is internally consistent. Transport (`ClosedEnv.WF_transport`) and preservation (`ClosedEnv.lookup_wf`, `ClosedEnv.assign_wf`) theorems mirror the `Environment` counterparts.

### State well-formedness (`State.WF`)

`State.WF` is a `structure` with two propositional fields: `env : st.env.WF st.mem` and `mem : st.mem.WF`. The structure form enables projection-based access (`h.env`, `h.mem`) in proofs. A companion `State.WF_iff` lemma converts between the structure form and a conjunction for rewriting.

### Key theorems

| Theorem | Statement |
|---|---|
| `Environment.WF_transport` | WF transports along the `Memory.LE` preorder: enlarging memory to a WF superset preserves environment WF. This is the bridge between WF and monotonicity. |
| `Environment.close_wf` | Closing the environment into a `ClosedEnv` snapshot preserves WF — the key lemma for `lambdaOk` and `Environment.lookup` scope case. |
| `Environment.lookup_transport` | A lookup result transports along the `Memory.LE` preorder: the looked-up value preserves its `SameShape` across memory growth (via `ClosedEnv.lookup_same_shape`). Used by `LValue.WF_transport`. |
| `Result.popEnv_wf` | Popping the environment frame after `case`/`scope` body evaluation preserves WF of the result (filters out escaping local l-values — see Model Adequacy Limits). |
| `evalAssign_wf` | Assignment preserves WF — the most involved preservation proof, handling variable slot vs box slot update paths. Also proves the RHS value equals the assigned r-value. |
| `Eval_result_wf` | **Capstone:** a well-formed state evaluates to a well-formed result. Structural induction over `Eval` (with a custom motive for `EvalList`). Proves both the result value and the resulting state are WF on `.ok` outcomes. |
| `EvalList_result_wf` | **Capstone:** the list counterpart of `Eval_result_wf`. Uses `Eval_result_wf` on the head element plus `EvalList_state_monotonic` to transport the tail's WF along the state growth. |

All remaining preservation theorems follow the same pattern: a step-level operation preserves WF on `.ok` outcomes.

### Design notes

- **Per-type WF predicates**: every semantic type has a dedicated `.WF` predicate over the relevant state/memory, with `@[simp]` lemmas unfolding each variant.
- **Transport theorems**: each memory-relevant per-type WF predicate has a `_transport` theorem moving it along the `Memory.LE`/`State.LE` preorder (enlarging memory to a WF superset preserves WF; `EnvValue.WF`/`EnvLookup.WF` transport through their containing `SimpleEnv`/`ClosedEnv` predicates instead). `LValue.WF_transport` is the most involved — it threads `Environment.SameShape` from `State.LE` through the lookup chain to show the looked-up r-value is preserved.
- **Proof style**: `fun_induction assign` for the recursive `Environment.assign` proofs (same pattern as `Monotonic.lean`). `grw` (guided rewrite) and `simp` over WF equalities are the standard memory-cell arguments. Error cases require no work (`Result.ok` is inconsistent with error hypotheses, so `simp at hr` dispatches them).
- **`caseOk`/`scope` proof pattern**: extract an existential from `Result.popEnv`, then reason about `Environment.pop` — an "unfold the pop, inspect the split" pattern.
- **Tight coupling to `Eval` rule shapes**: `Eval_result_wf`, `Eval_no_metatheory_error`, `Eval_state_closed`, and `Eval_no_name_error` pattern-match on every constructor of `Eval`/`EvalList`; any new rule requires extending these inductions.

## Static Well-Formedness (Value Categories)

The `Ast/WellFormed.lean` module defines `Category` (`val` | `ref (xs : Finset Ident)`)
and the mutual inductive judgment `Expr.WF : Expr → Category → Prop` (with its
`Definition.WF` companion) — the core analog of the spec's (§2.4) attribute judgment
`e : atr` over `Ref | Val | Void | Weak`. The judgment **derives** the value category
bottom-up: the core AST is post-attribution — a fixed AST — so the category is an
inferred property, not an input (top-down threading is the compiler's mechanism).
The goal (capstone not yet proven) is: **`e.WF .val` ⇒ evaluation of `e` never yields
`Error.lvalue`**.

### Design decisions (load-bearing for the future capstone)

- **Post-attribution core**: the Lean AST models the result of reference inference, so
  `Void`/`Weak` are gone (desugared by the front end — see Model Adequacy Limits); only
  the l-value/r-value split survives as `Category`.
- **Category profile**: the judgment derives the category **bottom-up** — leaves
  conclude their categories (`ref x` infers the exact singleton `.ref {x}` — the only
  variable name it can denote; `elemRef` infers the canonical empty `.ref {}` — an
  element l-value denotes no variable name, so binder disjointness never constrains it);
  every r-value producer concludes `.val` (with its subexpressions judged `.val`).
  Result-propagating forms: `seq` concludes its **second** component's category, with
  the first at an arbitrary (discarded) category; `ite`/`case`/`scope` are split into
  `Val`/`Ref` rule pairs by result category; `iteRef` concludes the **union** of its
  branch payloads (a ref/int-mixed `ite` is not derivable — matching the spec's
  `if … : a` same-attribute rule); `loop` always concludes `.val` (runtime `loopStop`
  yields the r-value ⊥) with its body at an arbitrary discarded category; `assign`
  concludes `.val` with the LHS judged at `.ref xs` for an arbitrary `xs` (names die
  at `:=`). The `.ref` category carries a `Finset Ident` payload — the set of variable
  names the position's result may denote; at `.val` there is no payload at all.
- **Local-lvalue escape check**: `case`/`scope` results pass through `Result.popEnv`,
  which rejects a `.lvalue (.var x)` whose `x` is bound by the popped frame (pattern
  binders / definition names). The predicate excludes this by **disjointness**:
  `caseRef` judges branch i at `.ref xs[i]` requiring `Disjoint xs[i] (pattern_i.vars.toFinset)`
  and concludes the union `.ref (Finset.univ.sup xs)`; `scopeRef` judges the body at
  `.ref xs` requiring `Disjoint xs (Definition.names ds).toFinset` and concludes the
  exact same `.ref xs`. This is exact w.r.t. `popEnv`: the runtime frame's keys are
  exactly the syntactic binder set (pattern vars / def names, dedup'd) and no
  body-reachable operation adds keys to the top frame. At `.val` (the `Val` rule pairs)
  no name conditions exist — by construction, there is no payload.
- **Deterministic category**: `Expr.WF_unique` proves that each expression derives at most one
  category — leaves conclude exact payloads, composite conclusions are fixed shapes or
  inherited/unioned from sub-derivations, and the arbitrary category/payload binders
  (`seq`'s first component, `loop`'s body, `assign`'s LHS payload) sit only in discarded
  positions. The same module also provides executable `Expr.inferCategory`/list and
  branch checks, together with `Decidable` instances for category well-formedness.
- **`assign` is `.val`-only with LHS `WF .ref`**: `:=` LHS parses at `Reff`, so an
  `assign` can never itself be an LHS (the SM compiler rejects non-`Ref`/`ElemRef` LHS).
- **Soundness in two directions** (both needed for the capstone, by mutual induction on
  `Eval`): `WF .val e ⇒` evaluation yields r-values only (no l-value reaches a sink),
  and `WF (.ref xs) e ⇒` evaluation yields l-values or errors, never an r-value, with
  every variable l-value result's name ∈ `xs` — the conclusion payload is the exact
  answer (`ref` contributes its singleton, `iteRef` unions its branches, `caseRef`
  unions per-branch payloads, `scopeRef`/`seq` pass their body/second component's
  payload through); the assign LHS premise is used only existentially
  (∃ xs, l.WF (.ref xs) — the l-value is consumed by `:=`, its name is irrelevant) —
  so `evalAssignR`'s `toLValue?` cannot
  fail on a `WF .ref` LHS and `popEnv` cannot reject at enclosing `case`/`scope`.
- **`commitCall` gap**: a closure **read from memory** may carry a body that is not
  `WF .val`; the syntactic half (all `fn`/`lambda` bodies are `.val`) is covered, but the
  transport needs a runtime invariant (the runtime `WellFormed.lean`'s
  `BoxValue.WF_closure` does **not** constrain closure bodies) — mirroring how
  `Eval_no_name_error` needs a well-formed closed state.
- Patterns are unconstrained (failed match is `.runtime`, not a category error); no
  lexical context is carried — name residence belongs to `Ast/Closed.lean`.

### `.lvalue` trigger-site coverage

Every trigger site of `Error.lvalue` in `Semantics/Eval.lean` is ruled out by a side
condition of `Expr.WF` — this is what makes the (future) capstone provable:

| Trigger site | Covered by |
|---|---|
| `evalBinop` `.eq`/`.ne` (direct `Value.toRValue?`), arith/cmp (via `Value.toInt?`), `.or`/`.and` (via `Value.toBool?`) | operands are `WF .val` |
| `evalElem` (`Value.toBox?`/`Value.toNat?`), `evalElemRef`, `evalAssign` RHS (`Value.toRValue?`), `chooseCase` scrutinee (`Value.toRValue?`) | those subexpressions are `WF .val` |
| `prepareCall` callee (`Value.toBox?`), `ite`/`loop` conditions (`Value.toBool?`) | those subexpressions are `WF .val` |
| `evalAssignR` LHS `Value.toLValue?` failure | LHS is `WF .ref` |
| `EvalList.err` (an l-value in an expression list) | the `arr`/`sexp`/`call` premises judge every element/callee/argument `.val` |
| `Result.popEnv` escaping local l-value | the `Disjoint` premises of the `caseRef`/`scopeRef` constructors |
| `commitCall` l-value returned by a function body | `Definition.fn`/`Expr.lambda` bodies are `WF .val` (see the `commitCall` gap above) |

- **Spec source caveat**: the visible rules in spec §2.4 (`spec/02.04.wellformedness.tex`
  upstream) are `Weak`-collapsed; the full four-attribute rule block (with the polymorphic
  `seq`/`if` rules) lives in that file's commented-out part and in the reference OCaml
  parser (`src/Language.ml`, the `atr` threading).
- **Parser guards**: an `Reff` position accepts only a variable or an element access
  (`notRef` guards + postfix-chain guard in `Language.ml`); the one way the reference front
  end puts an r-value form in an l-value position is the unary-minus quirk `-x[i] := v`
  (every engine then rejects it) — `WF` correctly rules such programs ill-formed.

## Closedness Invariant

The `Ast/Closed.lean` + `Semantics/Closed.lean` pair formalizes a **static closedness condition** and proves it sound against the runtime semantics: a closed expression evaluated in a well-formed closed state neither produces `.name` errors nor destroys closedness.

### Static side (`Lama/Ast/Closed.lean`)

- `Context` is a lexical context: a `Finmap` from `Ident` to `Bool` (`true` = variable binding, `false` = function definition). `Context.addVars` inserts variable bindings; `Context.addDef`/`addDefs` insert definition bindings with the appropriate flag (`var` → `true`, `fn` → `false`).
- `Expr.IsClosed ctx` is a structural predicate: every `.var x` requires `x ∈ ctx`, every `.ref x` requires `ctx.lookup x = .some true` (a **variable** binding — not just "bound"), `.lambda` and `Definition.fn` extend the context with parameters, `case` branches extend it with pattern binders (`Pattern.vars`), `scope` extends it with the definitions of the scope. Mutual companions `IsClosedList`/`IsClosedBranches`/`Definition.IsClosed`/`IsClosedList` handle the nested positions, with `_iff` simp lemmas flattening them to `∀ …, …` forms.

### Runtime side (`Lama/Semantics/Closed.lean`)

- Per-type `IsClosed` predicates extend closedness to runtime data: a `BoxValue.closure`'s captured `ClosedEnv` and body must be closed; `Memory.IsClosed` requires every cell closed; `State.IsClosed` (a structure with `mem`/`env` fields) ties them together.
- `X.context` derivations project a runtime `Context` out of `SimpleEnv`/`ClosedEnv`/`Environment`/`State` (names mapped to `isVar`). The bridge to the static side: `prepareDefList_env_context` (`ctx.addDefs ds = xs.context ∪ ctx`) and `evalPattern`-level lemmas show the runtime context after scope entry / pattern matching is exactly the statically predicted one.
- `State.context_transport` (`st.WF → st ≤ st' → st.context = st'.context`): the runtime context is **invariant under evaluation** — the key theorem making closedness propagable across sub-evaluations that grow the state.
- Transport theorems move `IsClosed`/`context` along `SameShape` and the `Memory.LE`/`State.LE` preorder; preservation theorems cover every step-level operation (the `_state_closed`/`_env_closed`/`_expr_closed` family for `evalVar`, `evalAssign`, `prepareCall`, `chooseCase`, `prepareDefList`).

### Key theorems

| Theorem | Statement |
|---|---|
| `State.context_transport` | The runtime context is invariant under state growth (`st.WF → st ≤ st' → st.context = st'.context`). Lets closedness of sub-expressions be checked against the unchanged context. |
| `prepareDefList_env_context` | `ctx.addDefs ds = xs.context ∪ ctx`: the environment pushed at scope entry has exactly the statically predicted context. |
| `Eval_state_closed` | **Capstone:** closedness is preserved by evaluation — a closed expression evaluated in a well-formed closed state yields a closed state. Structural induction over `Eval` with a custom motive for `EvalList`. |
| `Eval_no_name_error` | **Capstone** (`Error/Name.lean`): a closed expression evaluated in a well-formed closed state never yields `.err .name`. |

### Design notes

- The proof depends on the full invariant stack: WF (for `context_transport` and lookup well-formedness), monotonicity (`State.LE` to move contexts along sub-evaluations), and closedness itself. This mirrors the `Metatheory` module's dependency pattern: an error class is ruled out only relative to the invariant that makes its trigger sites unreachable.
- The step-level `_no_name_error` lemmas (`evalBinop`, `evalElem`, `evalElemRef`, `prepareCall`, `evalAssign`, `Environment.assign`, …) discharge the direct error sites; the induction over `Eval` threads closedness through the derivation tree, using `Eval_state_closed` + `State.context_transport` for the sub-evaluations.
- `prepareDefList`'s duplicate-name handling is load-bearing for soundness: a duplicate `var` (a name already claimed by a later definition in the same scope) generates **no** assignment, only the initializer's evaluation; for duplicate `fun` definitions the **last** one wins — earlier bodies silently vanish from the environment. Generating `assign (.ref x)` unconditionally would allow `ref x` to hit an `fn` binding at runtime (a `.name` error) inside a statically closed program — the very soundness violation the capstone rules out.

## Lean Technical Notes

- `DecidableEq` cannot be auto-derived for `Pattern` or the mutual `Expr`/`Scope`/`Definition` block (Lean limitation with nested inductives through `List`/`Option`/`×`). Workaround in-repo: `Pattern` gets a hand-written `DecidableEq` built from a private `beq`/`beqs` pair plus `beq_univ` biconditional; the mutual block has no `DecidableEq` at all
- The auto-generated induction principle for the mutual block is weak for nested positions; semantics code over nested positions needs well-founded recursion or a custom eliminator
- `Inhabited` exists on the mutual block (hand-written `instance : Inhabited Expr where default := .skip`; `Definition`/`Scope` derive from it)
- `Result`/`State`/`Environment` and most runtime semantic types derive no `Repr` — evaluation results cannot be inspected with `#eval`; use `simp`/`decide`-style proofs instead
- The determinism proof (`Unique.lean`) is a single structural induction over `Eval` with a custom mutual motive covering `EvalList` simultaneously (no standalone `EvalList_unique` theorem exists); `congr 1` is needed for the `caseOk`/`scope` cases because the rule conclusions apply `Result.popEnv`
- Marking `SameShape_symm`/`Rel_symm` as `@[simp]` causes unbounded metavariables (noted in the source comments of `Monotonic.lean`)
