import Lama.Ast.Pattern


namespace Lama.Ast

mutual

/-- Lama expressions -/
inductive Expr where
/-- Empty statement: skip -/
| skip
/-- Variable r-value reference -/
| var (x : Ident)
/-- Variable l-value reference -/
| ref (x : Ident)
/-- Integer constant -/
| int (n : ℤ)
/-- String literal -/
| str (s : String)
/-- Array literal: [E*] -/
| arr (xs : List Expr)
/-- S-expression: T(E*) -/
| sexp (t : Tag) (xs : List Expr)
/-- Lambda: fun (X*) {S} -/
| lambda (xs : List Ident) (b : Expr)
/-- Binary operator: E ⊗ E -/
| binop (op : Binop) (l r : Expr)
/-- Array element r-value access: E[E] -/
| elem (x i : Expr)
/-- Array element l-value access: E[E] -/
| elemRef (x i : Expr)
/-- Closure call: E(E*) -/
| call (x : Expr) (xs : List Expr)
/-- Assignment: E := E -/
| assign (l r : Expr)
/-- Sequential composition: E ; E -/
| seq (l r : Expr)
/-- Conditional: if E then E else E -/
| ite (c t e : Expr)
/-- While loop: while E do E -/
| loop (c b : Expr)
/-- Pattern matching: case E of (P -> E)+ esac -/
| case (x : Expr) (bs : List (Pattern × Expr))
/-- Nested scope: {S} -/
| scope (s : Scope)
deriving Repr

/-- Definition: variable or function -/
inductive Definition where
/-- Variable definition: var X [= E].
    Uses [skip] to omit initial value -/
| var (x : Ident) (y : Expr)
/-- Function definition: fun X (X*) {S} -/
| fn (x : Ident) (xs : List Ident) (b : Expr)
deriving Repr

/-- Scope expression: definitions followed by a body expression.
    S ::= D* E -/
structure Scope where
  defs : List Definition
  body : Expr
deriving Repr

end

instance : Inhabited Expr where
  default := .skip

deriving instance Inhabited for Definition, Scope

/-- A Lama compilation unit is a top-level scope expression. -/
abbrev Program := Scope
