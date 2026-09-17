import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Vector.Basic

import Lama.Ast.Closed


namespace Lama.Ast

inductive Category where
| val
| ref (xs : Finset Ident)
deriving DecidableEq, Inhabited

@[reducible]
def Definition.name
: Definition -> Ident
| .var x _ => x
| .fn x _ _ => x

@[reducible, simp]
def Definition.names
: List Definition -> List Ident
| [] => []
| d::ds => d.name :: Definition.names ds

mutual

inductive Expr.WF : Expr -> Category -> Prop
| skip : Expr.WF .skip .val
| var (x : Ident) : Expr.WF (.var x) .val
| ref (x : Ident) : Expr.WF (.ref x) (.ref {x})
| int (x : ℤ) : Expr.WF (.int x) .val
| str (s : String) : Expr.WF (.str s) .val
| arr (xs : List Expr) : (∀ x ∈ xs, x.WF .val) -> Expr.WF (.arr xs) .val
| sexp (t : Tag) (xs : List Expr) : (∀ x ∈ xs, x.WF .val) -> Expr.WF (.sexp t xs) .val
| lambda (xs : List Ident) (x : Expr) : x.WF .val -> Expr.WF (.lambda xs x) .val
| binop (op : Binop) (l r : Expr) : l.WF .val -> r.WF .val -> Expr.WF (.binop op l r) .val
| elem (x i : Expr) : x.WF .val -> i.WF .val -> Expr.WF (.elem x i) .val
| elemRef (x i : Expr) : x.WF .val -> i.WF .val -> Expr.WF (.elemRef x i) (.ref {})
| call (x : Expr) (xs : List Expr)
  : x.WF .val -> (∀ x ∈ xs, x.WF .val)
 -> Expr.WF (.call x xs) .val
| assign (l r : Expr) (xs : Finset Ident)
  : l.WF (.ref xs) -> r.WF .val
 -> Expr.WF (.assign l r) .val
| seq (l r : Expr) (cat₁ cat₂ : Category) : l.WF cat₁ -> r.WF cat₂ -> Expr.WF (.seq l r) cat₂
| iteVal (c t e : Expr) : c.WF .val -> t.WF .val -> e.WF .val -> Expr.WF (.ite c t e) .val
| iteRef (c t e : Expr) (xs ys : Finset Ident)
  : c.WF .val -> t.WF (.ref xs) -> e.WF (.ref ys)
 -> Expr.WF (.ite c t e) (.ref (xs ∪ ys))
| loop (c b : Expr) (cat : Category) : c.WF .val -> b.WF cat -> Expr.WF (.loop c b) .val
| caseVal (x : Expr) (bs : List (Pattern × Expr))
  : x.WF .val -> (∀ b ∈ bs, b.2.WF .val)
 -> Expr.WF (.case x bs) .val
| caseRef (x : Expr) (bs : List (Pattern × Expr))
          (xs : List.Vector (Finset Ident) bs.length)
  : x.WF .val -> 0 < bs.length
 -> (∀ i : Fin bs.length, bs[i].2.WF (.ref (xs.get i)))
 -> (∀ i : Fin bs.length, Disjoint (xs.get i) bs[i].1.vars.toFinset)
 -> Expr.WF (.case x bs) (.ref (Finset.univ.sup xs.get))
| scopeVal (ds : List Definition) (x : Expr)
  : (∀ d ∈ ds, d.WF) -> x.WF .val
 -> Expr.WF (.scope ⟨ ds, x ⟩) .val
| scopeRef (ds : List Definition) (x : Expr) (xs : Finset Ident)
  : (∀ d ∈ ds, d.WF) -> x.WF (.ref xs)
 -> Disjoint xs (Definition.names ds).toFinset
 -> Expr.WF (.scope ⟨ ds, x ⟩) (.ref xs)

inductive Definition.WF : Definition -> Prop
| var' (x : Ident) (e : Expr) : e.WF .val -> Definition.WF (.var x e)
| fn (x : Ident) (xs : List Ident) (b : Expr) : b.WF .val -> Definition.WF (.fn x xs b)

end

theorem Expr.WF_unique (e : Expr) (cat₁ cat₂ : Category)
                       (h₁ : e.WF cat₁) (h₂ : e.WF cat₂)
: cat₁ = cat₂ := by
  induction h₁
  using Expr.WF.rec (motive_2 := fun d _ => True)
  generalizing cat₂ with
  | skip =>
    cases h₂ with
    | skip => simp
  | var =>
    cases h₂ with
    | var => simp
  | ref =>
    cases h₂ with
    | ref => simp
  | int =>
    cases h₂ with
    | int => simp
  | str =>
    cases h₂ with
    | str => simp
  | arr =>
    cases h₂ with
    | arr => simp
  | sexp =>
    cases h₂ with
    | sexp => simp
  | lambda =>
    cases h₂ with
    | lambda => simp
  | binop =>
    cases h₂ with
    | binop => simp
  | elem =>
    cases h₂ with
    | elem => simp
  | elemRef =>
    cases h₂ with
    | elemRef => simp
  | call =>
    cases h₂ with
    | call => simp
  | assign =>
    cases h₂ with
    | assign => simp
  | seq l r catl₁ catr₁ hl₁ hr₁ ih₁ ih₂  =>
    cases h₂ with
    | seq _ catl₂ catr₂ _ hl₂ hr₂ =>
      apply ih₂
      assumption
  | iteVal c t e hc₁ ht₁ he₁ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | iteVal => simp
    | iteRef _ _ _ xs ys hc₂ ht₂ he₂ =>
      specialize ih₂ _ ht₂
      simp at ih₂
  | iteRef c t e xs ys hc₁ ht₁ he₁ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | iteVal _ _ _ hc₂ ht₂ he₂ =>
      specialize ih₂ _ ht₂
      simp at ih₂
    | iteRef _ _ _ xs ys hc₂ ht₂ he₂ =>
      specialize ih₂ _ ht₂
      specialize ih₃ _ he₂
      simp at ih₂ ih₃
      subst ih₂ ih₃
      simp
  | loop =>
    cases h₂ with
    | loop => simp
  | caseVal x bs hx₁ hbs ih₁ ih₂ =>
    cases h₂ with
    | caseVal => simp
    | caseRef _ _ xs hx₂ hbs₁ hbs₂ hbs₃ =>
      specialize hbs₂ ⟨ 0, hbs₁ ⟩
      specialize ih₂ _ ?_ _ hbs₂
      . simp
      simp at ih₂
  | caseRef x bs xs hx₁ hbs₁ hbs₂ hbs₃ ih₁ ih₂ =>
    cases h₂ with
    | caseVal _ _ hx₂ hbs =>
      specialize hbs bs[0] ?_
      . simp
      specialize ih₂ ⟨ 0, hbs₁ ⟩ _ hbs
      simp at ih₂
    | caseRef _ _ xs' hx₂ _ hbs₂' hbs₃' =>
      suffices xs = xs' by
        subst xs'
        simp
      ext1 i
      specialize hbs₂' i
      specialize ih₂ _ _ hbs₂'
      simp at ih₂
      exact ih₂
  | scopeVal ds x hds₁ hx₁ ih₁ ih₂ =>
    cases h₂ with
    | scopeVal => simp
    | scopeRef _ _ xs hds₂ hx₂ hds₂' =>
      specialize ih₂ _ hx₂
      simp at ih₂
  | scopeRef ds x xs hds₁ hx₁ hds₁' ih₁ ih₂ =>
    cases h₂ with
    | scopeVal _ _ hds₂ hx₂ =>
      specialize ih₂ _ hx₂
      simp at ih₂
    | scopeRef _ _ xs hds₂ hx₂ hds₂' =>
      specialize ih₂ _ hx₂
      simp at ih₂
      simp [ih₂]
  | var' => simp
  | fn => simp

inductive Expr.BranchesCategory (bs : List (Pattern × Expr)) where
| val : (∀ b ∈ bs, b.2.WF .val) -> BranchesCategory bs
| ref (xs : List.Vector (Finset Ident) bs.length)
: 0 < bs.length -> (∀ i : Fin bs.length, bs[i].2.WF (.ref (xs.get i)))
-> (∀ i : Fin bs.length, Disjoint (xs.get i) bs[i].1.vars.toFinset)
-> BranchesCategory bs

mutual

def Expr.inferCategory
: (e : Expr) -> { cat // e.WF cat } ⊕' (∀ cat, ¬ e.WF cat)
| .skip => .inl ⟨ .val, .skip ⟩
| .var _ => .inl ⟨ .val, .var _ ⟩
| .ref _ => .inl ⟨ .ref _, .ref _ ⟩
| .int _ => .inl ⟨ .val, .int _ ⟩
| .str _ => .inl ⟨ .val, .str _ ⟩
| .arr xs =>
  match Expr.checkCategoryList xs with
  | .isTrue h => .inl ⟨ .val, .arr xs h ⟩
  | .isFalse h => .inr fun
    | _, .arr _ h' => h h'
| .sexp _ xs =>
  match Expr.checkCategoryList xs with
  | .isTrue h => .inl ⟨ .val, .sexp _ xs h ⟩
  | .isFalse h => .inr fun
    | _, .sexp _ _ h' => h h'
| .lambda _ x =>
  match x.inferCategory with
  | .inl ⟨ .val, h ⟩ => .inl ⟨ .val, .lambda _ _ h ⟩
  | .inl ⟨ .ref _, h ⟩ => .inr fun
    | _, .lambda _ _ h' => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h => .inr fun
    | _, .lambda _ _ h' => h _ h'
| .binop _ l r =>
  match l.inferCategory, r.inferCategory with
  | .inl ⟨ .val, h₁ ⟩, .inl ⟨ .val, h₂ ⟩ => .inl ⟨ .val, .binop _ _ _ h₁ h₂ ⟩
  | .inl ⟨ .ref _, h ⟩, _ => .inr fun
    | _, .binop _ _ _ h' _ => nomatch Expr.WF_unique _ _ _ h h'
  | _, .inl ⟨ .ref _, h ⟩ => .inr fun
    | _, .binop _ _ _ _ h' => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h, _ => .inr fun
    | _, .binop _ _ _ h' _ => h _ h'
  | _, .inr h => .inr fun
    | _, .binop _ _ _ _ h' => h _ h'
| .elem x i =>
  match x.inferCategory, i.inferCategory with
  | .inl ⟨ .val, h₁ ⟩, .inl ⟨ .val, h₂ ⟩ => .inl ⟨ .val, .elem _ _ h₁ h₂ ⟩
  | .inl ⟨ .ref _, h ⟩, _ => .inr fun
    | _, .elem _ _ h' _ => nomatch Expr.WF_unique _ _ _ h h'
  | _, .inl ⟨ .ref _, h ⟩ => .inr fun
    | _, .elem _ _ _ h' => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h, _ => .inr fun
    | _, .elem _ _ h' _ => h _ h'
  | _, .inr h => .inr fun
    | _, .elem _ _ _ h' => h _ h'
| .elemRef x i =>
  match x.inferCategory, i.inferCategory with
  | .inl ⟨ .val, h₁ ⟩, .inl ⟨ .val, h₂ ⟩ => .inl ⟨ .ref _, .elemRef _ _ h₁ h₂ ⟩
  | .inl ⟨ .ref _, h ⟩, _ => .inr fun
    | _, .elemRef _ _ h' _ => nomatch Expr.WF_unique _ _ _ h h'
  | _, .inl ⟨ .ref _, h ⟩ => .inr fun
    | _, .elemRef _ _ _ h' => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h, _ => .inr fun
    | _, .elemRef _ _ h' _ => h _ h'
  | _, .inr h => .inr fun
    | _, .elemRef _ _ _ h' => h _ h'
| .call x xs =>
  match x.inferCategory, Expr.checkCategoryList xs with
  | .inl ⟨ .val, h₁ ⟩, .isTrue h₂ => .inl ⟨ .val, .call _ xs h₁ h₂ ⟩
  | .inl ⟨ .ref _, h ⟩, _ => .inr fun
    | _, .call _ _ h' _ => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h, _ => .inr fun
    | _, .call _ _ h' _ => h _ h'
  | _, .isFalse h => .inr fun
    | _, .call _ _ _ h' => h h'
| .assign l r =>
  match l.inferCategory, r.inferCategory with
  | .inl ⟨ .ref _, h₁ ⟩, .inl ⟨ .val, h₂ ⟩ => .inl ⟨ .val, .assign _ _ _ h₁ h₂ ⟩
  | .inl ⟨ .val, h ⟩, _ => .inr fun
    | _, .assign _ _ _ h' _ => nomatch Expr.WF_unique _ _ _ h h'
  | _, .inl ⟨ .ref _, h ⟩ => .inr fun
    | _, .assign _ _ _ _ h' => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h, _ => .inr fun
    | _, .assign _ _ _ h' _ => h _ h'
  | _, .inr h => .inr fun
    | _, .assign _ _ _ _ h' => h _ h'
| .seq l r =>
  match l.inferCategory, r.inferCategory with
  | .inl ⟨ _, h₁ ⟩, .inl ⟨ cat, h₂ ⟩ => .inl ⟨ cat, .seq _ _ _ _ h₁ h₂ ⟩
  | .inr h, _ => .inr fun
    | _, .seq _ _ _ _ h' _ => h _ h'
  | _, .inr h => .inr fun
    | _, .seq _ _ _ _ _ h' => h _ h'
| .ite c t e =>
  match c.inferCategory, t.inferCategory, e.inferCategory with
  | .inl ⟨ .val, h₁ ⟩, .inl ⟨ .val, h₂ ⟩, .inl ⟨ .val, h₃ ⟩ =>
    .inl ⟨ .val, .iteVal _ _ _ h₁ h₂ h₃ ⟩
  | _, .inl ⟨ .ref _, h₁ ⟩, .inl ⟨ .val, h₂ ⟩ => .inr fun
    | _, .iteVal _ _ _ _ h' _ => nomatch Expr.WF_unique _ _ _ h₁ h'
    | _, .iteRef _ _ _ _ _ _ _ h' => nomatch Expr.WF_unique _ _ _ h₂ h'
  | _, .inl ⟨ .val, h₁ ⟩, .inl ⟨ .ref _, h₂ ⟩ => .inr fun
    | _, .iteVal _ _ _ _ _ h' => nomatch Expr.WF_unique _ _ _ h₂ h'
    | _, .iteRef _ _ _ _ _ _ h' _ => nomatch Expr.WF_unique _ _ _ h₁ h'
  | .inl ⟨ .val, h₁ ⟩, .inl ⟨ .ref _, h₂ ⟩, .inl ⟨ .ref _, h₃ ⟩ =>
    .inl ⟨ .ref _, .iteRef _ _ _ _ _ h₁ h₂ h₃ ⟩
  | .inl ⟨ .ref _, h ⟩, _, _ => .inr fun
    | _, .iteVal _ _ _ h' _ _ => nomatch Expr.WF_unique _ _ _ h h'
    | _, .iteRef _ _ _ _ _ h' _ _ => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h, _, _ => .inr fun
    | _, .iteVal _ _ _ h' _ _ => h _ h'
    | _, .iteRef _ _ _ _ _ h' _ _ => h _ h'
  | _, .inr h, _ => .inr fun
    | _, .iteVal _ _ _ _ h' _ => h _ h'
    | _, .iteRef _ _ _ _ _ _ h' _ => h _ h'
  | _, _, .inr h => .inr fun
    | _, .iteVal _ _ _ _ _ h' => h _ h'
    | _, .iteRef _ _ _ _ _ _ _ h' => h _ h'
| .loop c b =>
  match c.inferCategory, b.inferCategory with
  | .inl ⟨ .val, h₁ ⟩, .inl ⟨ _, h₂ ⟩ => .inl ⟨ .val, .loop _ _ _ h₁ h₂ ⟩
  | .inl ⟨ .ref _, h ⟩, _ => .inr fun
    | _, .loop _ _ _ h' _ => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h, _ => .inr fun
    | _, .loop _ _ _ h' _ => h _ h'
  | _, .inr h => .inr fun
    | _, .loop _ _ _ _ h' => h _ h'
| .case x bs =>
  match x.inferCategory, Expr.inferCategoryBranches bs with
  | .inl ⟨ .val, h₁ ⟩, .inl (.val h₂) => .inl ⟨ .val, .caseVal _ _ h₁ h₂ ⟩
  | .inl ⟨ .val, h₁ ⟩, .inl (.ref xs h₂ h₃ h₄) => .inl ⟨ .ref _, .caseRef _ _ _ h₁ h₂ h₃ h₄ ⟩
  | .inl ⟨ .ref _, h ⟩, _ => .inr fun
    | _, .caseVal _ _ h' _ => nomatch Expr.WF_unique _ _ _ h h'
    | _, .caseRef _ _ _ h' _ _ _ => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h, _ => .inr fun
    | _, .caseVal _ _ h' _ => h _ h'
    | _, .caseRef _ _ _ h' _ _ _ => h _ h'
  | _, .inr h => .inr fun
    | _, .caseVal _ _ _ h' => h (.val h')
    | _, .caseRef _ _ _ _ h₁ h₂ h₃ => h (.ref _ h₁ h₂ h₃)
| .scope ⟨ ds, x ⟩ =>
  match Definition.isWFList ds, x.inferCategory with
  | .isTrue h₁, .inl ⟨ .val, h₂ ⟩ => .inl ⟨ .val, .scopeVal _ _ h₁ h₂ ⟩
  | .isTrue h₁, .inl ⟨ .ref xs, h₂ ⟩ =>
    if h : Disjoint xs (Definition.names ds).toFinset
    then .inl ⟨ .ref xs, .scopeRef _ _ _ h₁ h₂ h ⟩
    else .inr fun
      | _, .scopeVal _ _ _ h' => nomatch Expr.WF_unique _ _ _ h₂ h'
      | _, .scopeRef _ _ xs' _ h₃ h₄ => by
        have := Expr.WF_unique _ _ _ h₂ h₃
        simp at this
        subst this
        exact h h₄
  | .isFalse h, _ => .inr fun
    | _, .scopeVal _ _ h' _ => h h'
    | _, .scopeRef _ _ _ h' _ _ => h h'
  | _, .inr h => .inr fun
    | _, .scopeVal _ _ _ h' => h _ h'
    | _, .scopeRef _ _ _ _ h' _ => h _ h'

def Expr.checkCategoryList
: (xs : List Expr) -> Decidable (∀ x ∈ xs, x.WF .val)
| [] => .isTrue (by simp)
| x::xs =>
  match x.inferCategory, Expr.checkCategoryList xs with
  | .inl ⟨ .val, h₁ ⟩, .isTrue h₂ => .isTrue fun
    | _, .head _ => h₁
    | y, .tail _ h => h₂ y h
  | .inl ⟨ .ref _, h ⟩, _ => .isFalse fun h' =>
    nomatch Expr.WF_unique _ _ _ h (h' _ (.head _))
  | .inr h, _ => .isFalse fun h' => h _ (h' _ (.head _))
  | _, .isFalse h => .isFalse fun h' => h fun _ h => h' _ (.tail _ h)

def Expr.inferCategoryBranches
: (bs : List (Pattern × Expr))
-> Expr.BranchesCategory bs ⊕' (Expr.BranchesCategory bs -> False)
| [] => .inl $ .val (by simp)
| b::bs =>
  if hbs : bs = [] then
    match b.2.inferCategory with
    | .inl ⟨ .val, h ⟩ => .inl $ .val (by simp [h, hbs])
    | .inl ⟨ .ref xs, h ⟩ =>
      if h' : Disjoint xs b.1.vars.toFinset
      then by
        subst bs
        exact .inl $ .ref (.cons xs .nil) (by simp) (by simp [h]) (by simp [h'])
      else .inr fun
        | .val h'' => nomatch Expr.WF_unique _ _ _ h (h'' b (by simp))
        | .ref xs' _ h₁ h₂ => by
          subst bs
          let i : Fin 1 := ⟨ 0, by simp ⟩
          have := Expr.WF_unique _ _ _ h (h₁ i)
          simp at this
          subst this
          exact h' (h₂ i)
    | .inr h => .inr fun
      | .val h'' => h _ (h'' b (by simp))
      | .ref xs' _ h'' _ => h _ (h'' ⟨ 0, by simp ⟩)
  else
    match b.2.inferCategory, Expr.inferCategoryBranches bs with
    | .inl ⟨ .val, h₁ ⟩, .inl (.val h₂) => .inl $ .val fun
      | _, .head _ => h₁
      | _, .tail _ h => h₂ _ h
    | .inl ⟨ .val, h₁ ⟩, .inl (.ref _ h₂ h₃ _) => .inr fun
      | .val h => nomatch Expr.WF_unique _ _ _ (h bs[0] (by simp)) (h₃ ⟨ 0, h₂ ⟩)
      | .ref _ _ h _ => nomatch Expr.WF_unique _ _ _ (h ⟨ 0, by simp ⟩) h₁
    | .inl ⟨ .ref xs, h₁ ⟩, .inl (.val h₂) => .inr fun
      | .val h => nomatch Expr.WF_unique _ _ _ (h b (.head _)) h₁
      | .ref xs' _ h _ => by
        have : 0 < bs.length := by
          contrapose! hbs
          simp at hbs
          assumption
        have : 1 < (b :: bs).length := by simp [this]
        nomatch Expr.WF_unique _ _ .val (h ⟨ 1, this ⟩) (h₂ bs[0] (by simp))
    | .inl ⟨ .ref xs, h₁ ⟩, .inl (.ref ys _ h₂ h₃) =>
      if h' : Disjoint xs b.1.vars.toFinset
      then .inl $ .ref (xs ::ᵥ ys) (by simp) (fun
          | ⟨ 0, _ ⟩ => h₁
          | ⟨ i + 1, h₄ ⟩ => h₂ ⟨ i, by simp at h₄; exact h₄ ⟩
        ) (fun
          | ⟨ 0, _ ⟩ => h'
          | ⟨ i + 1, h₄ ⟩ => h₃ ⟨ i, by simp at h₄; exact h₄ ⟩
        )
      else .inr fun
        | .val h'' => nomatch Expr.WF_unique _ _ _ h₁ (h'' b (by simp))
        | .ref xs' _ h₄ h₅ => by
          let i : Fin (bs.length + 1) := ⟨ 0, by simp ⟩
          have := Expr.WF_unique _ _ _ h₁ (h₄ i)
          simp at this
          subst this
          exact h' (h₅ i)
    | .inr h, _ => .inr fun
      | .val h' => h _ (h' b (.head _))
      | .ref _ _ h' _ => h _ (h' ⟨ 0, by simp ⟩)
    | _, .inr h => .inr fun
      | .val h' => h $ .val fun b hb => h' b (.tail _ hb)
      | .ref xs h₁ h₂ h₃ =>
        have : 0 < bs.length := by
          contrapose! hbs
          simp at hbs
          assumption
        h $ .ref xs.tail this (fun i => by
          convert h₂ i.succ using 1
          simp
        ) (fun i => by
          convert h₃ i.succ using 1
          simp
        )

instance Definition.isWF
: (d : Definition) -> Decidable d.WF
| .var _ x =>
  match x.inferCategory with
  | .inl ⟨ .val, h ⟩ => .isTrue (.var' _ _ h)
  | .inl ⟨ .ref _, h ⟩ => .isFalse fun
    | .var' _ _ h' => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h => .isFalse fun
    | .var' _ _ h' => h _ h'
| .fn _ _ x =>
  match x.inferCategory with
  | .inl ⟨ .val, h ⟩ => .isTrue (.fn _ _ _ h)
  | .inl ⟨ .ref _, h ⟩ => .isFalse fun
    | .fn _ _ _ h' => nomatch Expr.WF_unique _ _ _ h h'
  | .inr h => .isFalse fun
    | .fn _ _ _ h' => h _ h'

def Definition.isWFList
: (xs : List Definition) -> Decidable (∀ x ∈ xs, x.WF)
| [] => .isTrue (by simp)
| d::ds =>
  match d.isWF, Definition.isWFList ds with
  | .isTrue h₁, .isTrue h₂ => .isTrue fun
    | _, .head _ => h₁
    | y, .tail _ h => h₂ y h
  | .isFalse h, _ => .isFalse fun h' => h (h' _ (.head _))
  | _, .isFalse h => .isFalse fun h' => h fun _ h => h' _ (.tail _ h)

end

instance (e : Expr)
: Decidable (∃ cat, e.WF cat) :=
  match e.inferCategory with
  | .inl ⟨ cat, h ⟩ => .isTrue ⟨ cat, h ⟩
  | .inr h => .isFalse fun ⟨ cat, h' ⟩ => h cat h'

instance (e : Expr) (cat : Category)
: Decidable (e.WF cat) :=
  match e.inferCategory with
  | .inl ⟨ cat', h₁ ⟩ =>
    if h₂ : cat = cat' then .isTrue $ h₂ ▸ h₁
    else .isFalse fun h => h₂ $ Expr.WF_unique _ _ _ h h₁
  | .inr h => .isFalse fun h' => h cat h'
