# lama-lean

`lama-lean` is a Lean 4 formalization of the dynamic semantics of
[Lama](https://github.com/PLTools/Lama), the Lambda-Algol language described by
the [v1.30 specification](https://github.com/PLTools/Lama/tree/1.30).

The project is a **semantic core for machine-checked reasoning**.  It defines a
Lean representation of Lama expressions, environments, memory, values, and
evaluation, then proves properties such as determinism, state monotonicity,
runtime well-formedness, closedness, and error soundness.

It is not a Lama compiler, parser, source interpreter, or runnable Lama
implementation.  There is currently no executable and no separate test suite;
the theorem development is the primary correctness evidence.

## Scope and non-goals

The model covers the core expression language and its dynamic semantics,
including:

- variables, references, assignments, scopes, functions, calls, arrays,
  strings, S-expressions, pattern matching, conditionals, loops, and built-in
  binary operators;
- an explicit heap-like memory and environment model;
- l-values versus r-values and classified evaluation errors;
- static closedness and value-category judgments; and
- preservation and soundness theorems connecting the static and runtime views.

The formalization deliberately does **not** attempt to model every part of the
upstream implementation.  In particular, it omits:

- parsing, pretty-printing, code generation, and I/O/effect traces;
- global variables, qualifiers, and the complete attribution/`VarKind` system;
- the upstream scheduling constructs (`Intrinsic` and `Control`); and
- compiler correctness or equivalence with any Lama backend.

These are design boundaries, rather than unfinished claims about the upstream
language.  See `AGENTS.md` for the detailed specification/implementation
comparison and model-adequacy notes.

## Quick start

### Prerequisites

Install Lean 4 and Lake with the toolchain recorded in `lean-toolchain`:

```text
leanprover/lean4:v4.28.0-rc1
```

The project depends on the matching `mathlib` revision.  A convenient setup is
the official Lean toolchain manager (`elan`) together with a working network
connection so Lake can fetch dependencies.

## Conceptual model

Evaluation is presented as an inductive relation rather than as an executable
interpreter.  A judgment relates an initial `State`, an expression, and either
an error or a result value plus a final state.  The state contains an
environment and a monotonically growing memory.  Values distinguish ordinary
integers from boxed values such as arrays, strings, S-expressions, and
closures; l-values are represented separately from r-values.

The main invariant stack is:

1. **Static categories** — `Expr.WF e c` records whether an expression is an
   r-value (`.val`) or may produce an l-value (`.ref xs`).
2. **Runtime well-formedness** — `State.WF` relates memory cells, boxes,
   closures, and environment structure.
3. **Static closedness** — `Expr.IsClosed` ensures referenced names are
   available in a lexical `Context` (and that `ref` names are variables).
4. **Runtime closedness** — `State.IsClosed` and context projections connect
   that static condition to captured environments and heap contents.
5. **Error soundness** — the preceding invariants make internal, name, and
   l-value errors unreachable in their respective settings.

Monotonicity is the bridge used throughout the stack: evaluation may allocate
and extend memory, but preserves the shape of existing cells and the relevant
environment context.  `State.context_transport` is especially important when
threading closedness through nested evaluations.

## Key results

The principal theorems include:

- `Eval_unique` — evaluation is deterministic.
- `Eval_state_monotonic` and `EvalList_state_monotonic` — successful evaluation
  only grows the state according to the semantic preorder.
- `Eval_result_wf` and `EvalList_result_wf` — well-formed states produce
  well-formed results and states.
- `Eval_category_wf` and `EvalList_category_wf` — runtime results respect the
  static value category and its runtime invariant.
- `Eval_state_closed` and `EvalList_state_closed` — evaluation preserves
  closedness.
- `Eval_no_metatheory_error` — internal metatheory errors cannot arise from a
  well-formed evaluation.
- `Eval_no_name_error` — closed evaluation in a well-formed closed state cannot
  produce a `.name` error.
- `Eval_no_lvalue_error` — category-well-formed evaluation cannot produce a
  `.lvalue` error.

Useful supporting results include `prepareDefList_env_context`, which relates
scope-definition initialization to the static context, and
`State.context_transport`, which preserves that context across state growth.

The remaining runtime error classes are `.type` and `.runtime`: they describe
type/shape mismatches and runtime conditions such as invalid indices or failed
pattern matches in the accepted model.

## Important limitations

The Lean model intentionally differs from one or more upstream engines in
several observable edge cases:

- I/O and effects are absent, so no input/output behavior is specified.
- Equality on mixed boxed/unboxed values uses the model's `RValue` equality;
  it does not reproduce all interpreter, stack-machine, or x86 behavior.
- Division and remainder by zero are totalized by the Lean model, rather than
  modeling the traps raised by compiled engines.
- Escaping local l-values are rejected when a scope/case frame is popped.  This
  is stricter than the compiled backends and follows the reference/interpreter
  side of the intended semantics.
- Closure capture and write-back are modeled according to the documented core
  design, but details can differ from the interpreter's object-level behavior.
- The AST is post-attribution and omits several source-language distinctions;
  a front end translating source Lama into this core is outside this repository.

Consequently, the theorems here are not a full compiler-correctness theorem and
should not be read as proving that compiled Lama programs behave identically to
this Lean relation in every case.

## Where to start reading

For a first pass, read these files in order:

1. `Lama/Ast/Expr.lean` to learn the core syntax.
2. `Lama/Semantics/Eval.lean` to see the runtime data and evaluation rules.
3. `Lama/Semantics/Unique.lean` for a self-contained metatheoretic proof using
   structural induction over the evaluation relation.
4. `Lama/Semantics/Monotonic.lean` and `Lama/Semantics/WellFormed.lean` for
   the state invariants.
5. `Lama/Ast/Closed.lean` followed by `Lama/Semantics/Closed.lean` for the
   static/runtime closedness connection.
6. The three `Semantics/Error/` modules for the error-soundness capstones.

When investigating a theorem, search for its declaration and then inspect the
nearby helper lemmas: the preservation proofs are intentionally structured
around the step-level operations in `Eval.lean`.  The upstream v1.30
specification is the authority for source-language intent, while the OCaml
implementation is useful for understanding the documented divergences.

## Repository map

### Abstract syntax and static judgments

- `Lama/Ast/Ident.lean` — identifiers, tags, and the closed enumeration of
  built-in binary operators.
- `Lama/Ast/Pattern.lean` — patterns and value-type tags.
- `Lama/Ast/Expr.lean` — mutually defined expressions, scopes, definitions,
  and `Program`.
- `Lama/Ast/Closed.lean` — lexical `Context` and static closedness judgments.
- `Lama/Ast/WellFormed.lean` — static value categories (`val` and `ref xs`)
  and the `Expr.WF` judgment, including executable inference.
- `Lama/Ast.lean` — AST umbrella module.

### Runtime semantics and metatheory

- `Lama/Semantics/Eval.lean` — runtime values, memory/environment helpers,
  errors, and the `Eval`/`EvalList` relations.
- `Lama/Semantics/Unique.lean` — determinism of evaluation.
- `Lama/Semantics/Monotonic.lean` — shape relations and the `Memory.LE` /
  `State.LE` preorder.
- `Lama/Semantics/WellFormed.lean` — runtime well-formedness and preservation.
- `Lama/Semantics/Category.lean` — runtime category soundness.
- `Lama/Semantics/Closed.lean` — runtime closedness and context transport.
- `Lama/Semantics/Error/Metatheory.lean` — exclusion of internal invariant
  failures.
- `Lama/Semantics/Error/Name.lean` — exclusion of name-resolution failures
  for closed programs.
- `Lama/Semantics/Error/LValue.lean` — exclusion of l-value-category failures
  for category-well-formed programs.
- `Lama/Semantics.lean` — semantics umbrella module.
- `Lama.lean` — project-wide umbrella module.

### Build the library

From the repository root, run:

```sh
lake exe cache get   # optional, but recommended: download prebuilt mathlib artifacts
lake build
```

The cache command requires network access and can save a substantial amount of
time on a fresh checkout.  If the cache is unavailable, `lake build` can still
build the required dependencies from source.

The root umbrella module can be imported in a Lean file with:

```lean
import Lama
```

`Lama.lean` imports both `Lama.Ast` and `Lama.Semantics`.
