import Mathlib


namespace Lama.Ast

/-- Identifier -/
structure Ident where
  name : String
deriving Repr, DecidableEq, Inhabited, Hashable

theorem Ident.name_inj : Function.Injective Ident.name := by
  intro x y h
  obtain ⟨ x ⟩ := x
  obtain ⟨ y ⟩ := y
  simp at *
  assumption

@[reducible]
instance : LinearOrder Ident :=
  .lift' Ident.name Ident.name_inj

/-- S-expression constructor tag -/
structure Tag where
  name : String
deriving Repr, DecidableEq, Inhabited, Hashable

/-- Infix operator -/
inductive Binop where
| or | and
| eq | ne | le | lt | ge | gt
| add | sub | mul | quot | rem
deriving Repr, DecidableEq, Inhabited, Hashable
