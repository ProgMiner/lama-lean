# lama-lean

A Lean 4 formalization of the [Lama](https://github.com/PLTools/Lama) programming language (Lambda-Algol, v1.30) — a *semantic core* for reasoning about the dynamic semantics of Lama programs (determinism, monotonicity, well-formedness, closedness, and error-class soundness proofs). See `AGENTS.md` for the detailed project notes: known spec-vs-implementation divergences, intentional AST design decisions, and model adequacy limits.

## Build

Toolchain: `leanprover/lean4:v4.28.0-rc1` (see `lean-toolchain`), with a mathlib dependency.

```
lake build Lama
```

Note: plain `lake build` fails — `defaultTargets = ["lama"]` in `lakefile.toml` points at a commented-out executable stub, and the only real target is the `Lama` lean_lib.
