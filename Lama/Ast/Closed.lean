import Mathlib.Data.Finmap

import Lama.Ast.Expr


namespace Lama.Ast

-- lexical context, `false` designates function definitions
abbrev Context := Finmap fun (_ : Ident) => Bool

@[reducible, simp]
def Context.addVars (ctx : Context)
: List Ident -> Context
| [] => ctx
| x::xs => addVars (ctx.insert x true) xs

@[reducible]
def Context.addDef (ctx : Context)
: Definition -> Context
| .var x _ => ctx.insert x true
| .fn x _ _ => ctx.insert x false

@[reducible, simp]
def Context.addDefs (ctx : Context)
: List Definition -> Context
| [] => ctx
| d::ds => addDefs (ctx.addDef d) ds

mutual

@[reducible]
def Pattern.vars
: Pattern -> List Ident
| wildcard => []
| const _ => []
| string _ => []
| array ps => listVars ps
| sexp _ ps => listVars ps
| named x p => x::p.vars
| boxTag => []
| valTag => []
| strTag => []
| sexpTag => []
| arrayTag => []
| funTag => []

@[reducible, simp]
def Pattern.listVars
: List Pattern -> List Ident
| [] => []
| p::ps => listVars ps ++ p.vars

end

mutual

@[reducible, simp]
def Expr.IsClosed (ctx : Context)
: Expr -> Prop
| .skip => True
| .var x => x ∈ ctx
| .ref x => ctx.lookup x = .some true
| .int _ => True
| .str _ => True
| .arr xs => Expr.IsClosedList ctx xs
| .sexp _ xs => Expr.IsClosedList ctx xs
| .lambda xs b => b.IsClosed (ctx.addVars xs)
| .binop _ l r => l.IsClosed ctx ∧ r.IsClosed ctx
| .elem x i => x.IsClosed ctx ∧ i.IsClosed ctx
| .elemRef x i => x.IsClosed ctx ∧ i.IsClosed ctx
| .call x xs => x.IsClosed ctx ∧ Expr.IsClosedList ctx xs
| .assign l r => l.IsClosed ctx ∧ r.IsClosed ctx
| .seq l r => l.IsClosed ctx ∧ r.IsClosed ctx
| .ite c t e => c.IsClosed ctx ∧ t.IsClosed ctx ∧ e.IsClosed ctx
| .loop c b => c.IsClosed ctx ∧ b.IsClosed ctx
| .case x bs => x.IsClosed ctx ∧ Expr.IsClosedBranches ctx bs
| .scope ⟨ ds, b ⟩ =>
  let ctx := ctx.addDefs ds
  b.IsClosed ctx ∧ Definition.IsClosedList ctx ds

@[reducible, simp]
def Expr.IsClosedList (ctx : Context)
: List Expr -> Prop
| [] => True
| x::xs => x.IsClosed ctx ∧ Expr.IsClosedList ctx xs

@[reducible, simp]
def Expr.IsClosedBranches (ctx : Context)
: List (Pattern × Expr) -> Prop
| [] => True
| (p, b)::bs => b.IsClosed (ctx.addVars p.vars) ∧ Expr.IsClosedBranches ctx bs

@[reducible, simp]
def Definition.IsClosed (ctx : Context)
: Definition -> Prop
| .var _ e => e.IsClosed ctx
| .fn _ xs b => b.IsClosed (ctx.addVars xs)

@[reducible, simp]
def Definition.IsClosedList (ctx : Context)
: List Definition -> Prop
| [] => True
| d::ds => d.IsClosed ctx ∧ Definition.IsClosedList ctx ds

end

@[simp]
theorem Expr.IsClosedList_iff (ctx : Context)
                              (es : List Expr)
: IsClosedList ctx es <-> (∀ e ∈ es, e.IsClosed ctx) where
  mp h := by
    induction es with
    | nil => simp
    | cons e es ih =>
      simp [h]
      apply ih
      simp [h]
  mpr h := by
    induction es with
    | nil => simp
    | cons e es ih =>
      simp [h]
      apply ih
      intro e' he'
      apply h
      simp [he']

@[simp]
theorem Expr.IsClosedBranches_iff (ctx : Context)
                                  (bs : List (Pattern × Expr))
: IsClosedBranches ctx bs <-> (∀ b ∈ bs, b.2.IsClosed (ctx.addVars b.1.vars)) where
  mp h := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp [h, -Prod.forall]
      apply ih
      simp [h]
  mpr h := by
    induction bs with
    | nil => simp
    | cons e es ih =>
      simp [h]
      apply ih
      intro e' he'
      apply h
      simp [he']

@[simp]
theorem Definition.IsClosedList_iff (ctx : Context)
                                    (ds : List Definition)
: IsClosedList ctx ds <-> (∀ d ∈ ds, d.IsClosed ctx) where
  mp h := by
    induction ds with
    | nil => simp
    | cons d ds ih =>
      simp [h]
      apply ih
      simp [h]
  mpr h := by
    induction ds with
    | nil => simp
    | cons d ds ih =>
      simp [h]
      apply ih
      intro d' hd'
      apply h
      simp [hd']

mutual

instance Expr.isClosed (ctx : Context)
: (x : Expr) -> Decidable (x.IsClosed ctx)
| .skip => inferInstance
| .var _ => inferInstance
| .ref _ => inferInstance
| .int _ => inferInstance
| .str _ => inferInstance
| .arr xs => Expr.isClosedList ctx xs
| .sexp _ xs => Expr.isClosedList ctx xs
| .lambda xs b => b.isClosed (ctx.addVars xs)
| .binop _ l r => @instDecidableAnd _ _ (l.isClosed ctx) (r.isClosed ctx)
| .elem x i => @instDecidableAnd _ _ (x.isClosed ctx) (i.isClosed ctx)
| .elemRef x i => @instDecidableAnd _ _ (x.isClosed ctx) (i.isClosed ctx)
| .call x xs => @instDecidableAnd _ _ (x.isClosed ctx) (Expr.isClosedList ctx xs)
| .assign l r => @instDecidableAnd _ _ (l.isClosed ctx) (r.isClosed ctx)
| .seq l r => @instDecidableAnd _ _ (l.isClosed ctx) (r.isClosed ctx)
| .ite c t e =>
  @instDecidableAnd _ _ (c.isClosed ctx)
    $ @instDecidableAnd _ _ (t.isClosed ctx) (e.isClosed ctx)
| .loop c b => @instDecidableAnd _ _ (c.isClosed ctx) (b.isClosed ctx)
| .case x bs =>
  @instDecidableAnd _ _ (x.isClosed ctx)
    $ Expr.isClosedBranches ctx bs
| .scope ⟨ ds, x ⟩ =>
  @instDecidableAnd _ _ (x.isClosed (ctx.addDefs ds))
    $ Definition.isClosedList (ctx.addDefs ds) ds

instance Expr.isClosedList (ctx : Context)
: (xs : List Expr) -> Decidable (Expr.IsClosedList ctx xs)
| [] => .isTrue (by simp)
| x::xs => @instDecidableAnd _ _ (x.isClosed ctx) (Expr.isClosedList ctx xs)

instance Expr.isClosedBranches (ctx : Context)
: (bs : List (Pattern × Expr)) -> Decidable (Expr.IsClosedBranches ctx bs)
| [] => .isTrue (by simp)
| (p, x)::bs =>
  @instDecidableAnd _ _ (x.isClosed (ctx.addVars p.vars))
    $ Expr.isClosedBranches ctx bs

instance Definition.isClosed (ctx : Context)
: (d : Definition) -> Decidable (d.IsClosed ctx)
| .var _ x => x.isClosed ctx
| .fn _ xs b => b.isClosed (ctx.addVars xs)

instance Definition.isClosedList (ctx : Context)
: (ds : List Definition) -> Decidable (Definition.IsClosedList ctx ds)
| [] => .isTrue (by simp)
| d::ds =>
  @instDecidableAnd _ _ (d.isClosed ctx)
    $ Definition.isClosedList ctx ds

end
