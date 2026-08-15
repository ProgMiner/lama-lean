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

mutual

private theorem Pattern.beq_univ (p q : Pattern)
: beq p q <-> p = q :=
  match p, q with
  | wildcard, wildcard => by simp
  | wildcard, const m => by simp
  | wildcard, string t => by simp
  | wildcard, array qs => by simp
  | wildcard, sexp u qs => by simp
  | wildcard, named y q => by simp
  | wildcard, boxTag => by simp
  | wildcard, valTag => by simp
  | wildcard, strTag => by simp
  | wildcard, sexpTag => by simp
  | wildcard, arrayTag => by simp
  | wildcard, funTag => by simp
  | const n, wildcard => by simp
  | const n, const m => by simp
  | const n, string t => by simp
  | const n, array qs => by simp
  | const n, sexp u qs => by simp
  | const n, named y q => by simp
  | const n, boxTag => by simp
  | const n, valTag => by simp
  | const n, strTag => by simp
  | const n, sexpTag => by simp
  | const n, arrayTag => by simp
  | const n, funTag => by simp
  | string s, wildcard => by simp
  | string s, const m => by simp
  | string s, string t => by simp
  | string s, array qs => by simp
  | string s, sexp u qs => by simp
  | string s, named y q => by simp
  | string s, boxTag => by simp
  | string s, valTag => by simp
  | string s, strTag => by simp
  | string s, sexpTag => by simp
  | string s, arrayTag => by simp
  | string s, funTag => by simp
  | array ps, wildcard => by simp
  | array ps, const m => by simp
  | array ps, string t => by simp
  | array ps, array qs => by simp [beqs_univ]
  | array ps, sexp u qs => by simp
  | array ps, named y q => by simp
  | array ps, boxTag => by simp
  | array ps, valTag => by simp
  | array ps, strTag => by simp
  | array ps, sexpTag => by simp
  | array ps, arrayTag => by simp
  | array ps, funTag => by simp
  | sexp t ps, wildcard => by simp
  | sexp t ps, const m => by simp
  | sexp t ps, string _ => by simp
  | sexp t ps, array qs => by simp
  | sexp t ps, sexp u qs => by simp [beqs_univ]
  | sexp t ps, named y q => by simp
  | sexp t ps, boxTag => by simp
  | sexp t ps, valTag => by simp
  | sexp t ps, strTag => by simp
  | sexp t ps, sexpTag => by simp
  | sexp t ps, arrayTag => by simp
  | sexp t ps, funTag => by simp
  | named x p, wildcard => by simp
  | named x p, const m => by simp
  | named x p, string t => by simp
  | named x p, array qs => by simp
  | named x p, sexp u qs => by simp
  | named x p, named y q => by simp [beq_univ]
  | named x p, boxTag => by simp
  | named x p, valTag => by simp
  | named x p, strTag => by simp
  | named x p, sexpTag => by simp
  | named x p, arrayTag => by simp
  | named x p, funTag => by simp
  | boxTag, wildcard => by simp
  | boxTag, const m => by simp
  | boxTag, string t => by simp
  | boxTag, array qs => by simp
  | boxTag, sexp u qs => by simp
  | boxTag, named y q => by simp
  | boxTag, boxTag => by simp
  | boxTag, valTag => by simp
  | boxTag, strTag => by simp
  | boxTag, sexpTag => by simp
  | boxTag, arrayTag => by simp
  | boxTag, funTag => by simp
  | valTag, wildcard => by simp
  | valTag, const m => by simp
  | valTag, string t => by simp
  | valTag, array qs => by simp
  | valTag, sexp u qs => by simp
  | valTag, named y q => by simp
  | valTag, boxTag => by simp
  | valTag, valTag => by simp
  | valTag, strTag => by simp
  | valTag, sexpTag => by simp
  | valTag, arrayTag => by simp
  | valTag, funTag => by simp
  | strTag, wildcard => by simp
  | strTag, const m => by simp
  | strTag, string t => by simp
  | strTag, array qs => by simp
  | strTag, sexp u qs => by simp
  | strTag, named y q => by simp
  | strTag, boxTag => by simp
  | strTag, valTag => by simp
  | strTag, strTag => by simp
  | strTag, sexpTag => by simp
  | strTag, arrayTag => by simp
  | strTag, funTag => by simp
  | sexpTag, wildcard => by simp
  | sexpTag, const m => by simp
  | sexpTag, string t => by simp
  | sexpTag, array qs => by simp
  | sexpTag, sexp u qs => by simp
  | sexpTag, named y q => by simp
  | sexpTag, boxTag => by simp
  | sexpTag, valTag => by simp
  | sexpTag, strTag => by simp
  | sexpTag, sexpTag => by simp
  | sexpTag, arrayTag => by simp
  | sexpTag, funTag => by simp
  | arrayTag, wildcard => by simp
  | arrayTag, const m => by simp
  | arrayTag, string t => by simp
  | arrayTag, array qs => by simp
  | arrayTag, sexp u qs => by simp
  | arrayTag, named y q => by simp
  | arrayTag, boxTag => by simp
  | arrayTag, valTag => by simp
  | arrayTag, strTag => by simp
  | arrayTag, sexpTag => by simp
  | arrayTag, arrayTag => by simp
  | arrayTag, funTag => by simp
  | funTag, wildcard => by simp
  | funTag, const m => by simp
  | funTag, string t => by simp
  | funTag, array qs => by simp
  | funTag, sexp u qs => by simp
  | funTag, named y q => by simp
  | funTag, boxTag => by simp
  | funTag, valTag => by simp
  | funTag, strTag => by simp
  | funTag, sexpTag => by simp
  | funTag, arrayTag => by simp
  | funTag, funTag => by simp

private theorem Pattern.beqs_univ (ps qs : List Pattern)
: beqs ps qs <-> ps = qs :=
  match ps, qs with
  | [], [] => by simp
  | [], q::qs => by simp
  | p::ps, [] => by simp
  | p::ps, q::qs => by simp [beq_univ, beqs_univ]

end

instance : DecidableEq Pattern := by
  intro p q
  cases h : Pattern.beq p q with
  | true => right; rw [<-Pattern.beq_univ]; assumption
  | false => left; rw [<-Pattern.beq_univ]; simp [h]
