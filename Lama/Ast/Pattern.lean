import Lama.Ast.Ident

namespace Lama.Ast

/-- Patterns in Lama's case-expressions and function-argument desugaring -/
inductive Pattern where
/-- Wildcard: _ -/
| wildcard
/-- Integer constant pattern -/
| const (n : Int)
/-- String constant pattern -/
| string (s : String)
/-- Array pattern: [P*] -/
| array (elems : List Pattern)
/-- S-expression pattern: T(P*) -/
| sexp (tag : Tag) (args : List Pattern)
/-- Named/bind pattern: x@p (bare binder x is encoded as x@wildcard) -/
| named (x : Ident) (pat : Pattern)
/-- Type-tag patterns (shape tests) -/
| boxTag    -- #box (reference)
| valTag    -- #val (value)
| strTag    -- #str
| sexpTag   -- #sexp
| arrayTag  -- #array
| funTag    -- #fun
deriving Repr, Inhabited

abbrev Pattern.name (x : Ident) : Pattern :=
  named x wildcard

mutual

@[reducible, simp]
private def Pattern.beq : Pattern -> Pattern -> Bool
| wildcard, wildcard => true
| const n, const m => n = m
| string s, string t => s = t
| array ps₁, array ps₂ => beqs ps₁ ps₂
| sexp t ps₁, sexp u ps₂ => t = u && beqs ps₁ ps₂
| named x p, named y q => x = y && beq p q
| boxTag, boxTag => true
| valTag, valTag => true
| strTag, strTag => true
| sexpTag, sexpTag => true
| arrayTag, arrayTag => true
| funTag, funTag => true
| _, _ => false

@[reducible, simp]
private def Pattern.beqs : List Pattern -> List Pattern -> Bool
| [], [] => true
| p₁::ps₁, p₂::ps₂ => beq p₁ p₂ && beqs ps₁ ps₂
| _, _ => false

end

private theorem Pattern.beq_univ (p q : Pattern)
: beq p q <-> p = q := by
  induction p
  using Pattern.rec (motive_2 := fun ps => (qs : _) -> beqs ps qs <-> ps = qs)
  generalizing q
  all_goals try cases q <;> simp [*]
  case nil qs => cases qs <;> simp
  case cons qs => cases qs <;> simp [*]

instance : DecidableEq Pattern := by
  intro p q
  cases h : Pattern.beq p q with
  | true => right; rw [<-Pattern.beq_univ]; assumption
  | false => left; rw [<-Pattern.beq_univ]; simp [h]
