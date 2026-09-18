import Lama.Semantics.Category
import Lama.Semantics.Closed


namespace Lama.Semantics

open Ast

@[simp]
theorem RValue.toNat?_no_lvalue_error (x : RValue)
: x.toNat? ≠ .error .lvalue := by
  unfold toNat?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ -, rfl ⟩ := h
  simp

theorem SimpleEnv.SameShape_mem (xs ys : SimpleEnv)
                                (h : xs.SameShape ys)
: ∀ x, x ∈ xs <-> x ∈ ys := by
  revert xs ys h
  suffices ∀ (xs ys : SimpleEnv), xs.SameShape ys -> ∀ x ∈ xs, x ∈ ys by
    intro xs ys h x
    constructor <;> intro hx <;> apply this _ _ _ _ hx
    . assumption
    . symm
      assumption
  intro xs ys h x hx
  rw [Finmap.mem_iff] at hx
  obtain ⟨ y, hx ⟩ := hx
  unfold SameShape at h
  specialize h x
  rw [hx] at h
  simp at h
  obtain ⟨ y', h, - ⟩ := h
  simp [Finmap.mem_iff, h]

theorem BoxValue.assign_no_lvalue_error (x : BoxValue) (i : ℕ) (y : RValue)
: x.assign i y ≠ .error .lvalue := by
  unfold assign
  cases x with
  | undefined => simp
  | str =>
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
    split <;> try simp
    . rename_i h
      contrapose! h
      subst h
      simp
    split <;> simp
    rename_i h
    contrapose! h
    subst h
    simp
  | arr =>
    simp [Functor.map, Except.map]
    split <;> simp
    rename_i h
    contrapose! h
    subst h
    simp
  | sexp =>
    simp [Functor.map, Except.map]
    split <;> simp
    rename_i h
    contrapose! h
    subst h
    simp
  | closure => simp

theorem Environment.lookup_no_lvalue_error (mem : Memory) (env : Environment) (x : Ident)
: env.lookup x mem ≠ .error .lvalue := by
  fun_induction lookup with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 =>
    simp [Functor.map, Except.map]
    split <;> simp
    rename_i h
    simp at h
    obtain ⟨ h, rfl ⟩ := h
    simp
  | case5 xs env h ih => apply ih

theorem Environment.assign_no_lvalue_error (mem : Memory) (env : Environment)
                                           (x : Ident) (y : RValue)
: env.assign x y mem ≠ .error .lvalue := by
  fun_induction assign with
  | case1 => simp
  | case2 =>
    simp [Functor.map, Except.map]
    split <;> simp
    rename_i h
    simp at h
    obtain ⟨ -, rfl ⟩ := h
    simp
  | case3 => simp
  | case4 => simp
  | case5 => simp
  | case6 xs env h ih =>
    simp [Functor.map, Except.map]
    split <;> simp
    rename_i h
    contrapose! h
    subst h
    apply ih

@[simp]
theorem Value.toRValue?_none (x : Value)
: x.toRValue? = .none <-> ∃ x', x = .lvalue x' := by
  cases x <;> simp

@[simp]
theorem Value.toLValue?_none (x : Value)
: x.toLValue? = .none <-> ∃ x', x = .rvalue x' := by
  cases x <;> simp

@[simp]
theorem Value.toInt?_lvalue_error (x : Value)
: x.toInt? = .error .lvalue <-> ∃ x', x = .lvalue x' := by
  unfold toInt?
  simp [Bind.bind, Except.bind]
  split <;> simp
  . rename_i h
    simp at h
    simp [h]
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem Value.toNat?_lvalue_error (x : Value)
: x.toNat? = .error .lvalue <-> ∃ x', x = .lvalue x' := by
  unfold toNat?
  simp [Bind.bind, Except.bind]
  split <;> try simp
  . rename_i h
    simp at h
    simp [h]
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem Value.toBool?_lvalue_error (x : Value)
: x.toBool? = .error .lvalue <-> ∃ x', x = .lvalue x' := by
  unfold toBool?
  simp [Bind.bind, Except.bind]
  split <;> try simp
  . rename_i h
    simp at h
    simp [h]
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem Value.toBox?_lvalue_error (x : Value)
: x.toBox? = .error .lvalue <-> ∃ x', x = .lvalue x' := by
  unfold toBox?
  simp [Bind.bind, Except.bind]
  split <;> try simp
  . rename_i h
    simp at h
    simp [h]
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

theorem Result.popEnv_lvalue_error (r : Result Value)
                                   (h : r.popEnv = .err .lvalue)
: r = .err .lvalue ∨ ∃ xs env x st, r = .ok (.lvalue (.var x)) st
                                  ∧ st.env = .scope xs env ∧ x ∈ xs
:= by
  unfold popEnv at h
  cases r <;> simp at h
  on_goal 2 => simp [h]
  right
  split at h <;> simp at h
  . rename_i h'
    simp [h']
    split at h <;> simp at h <;> assumption
  split at h <;> simp at h

theorem evalVar_no_lvalue_error (st : State) (x : Ident)
: evalVar st x ≠ .error .lvalue := by
  unfold evalVar
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    apply Environment.lookup_no_lvalue_error
  split <;> simp

theorem checkRef_no_some_lvalue (st : State) (x : Ident)
: checkRef st x ≠ .some .lvalue := by
  unfold checkRef
  split <;> simp
  rename_i h
  contrapose! h
  subst h
  apply Environment.lookup_no_lvalue_error

theorem evalBinop_lvalue_error (x y : Value) (op : Binop)
                               (h : evalBinop x y op = .error .lvalue)
: (∃ x', x = .lvalue x') ∨ (∃ y', y = .lvalue y') := by
  unfold evalBinop at h
  cases op <;> simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  all_goals split at h <;> try simp at h
  all_goals try split at h <;> simp at h
  all_goals
    subst h
    rename_i h
    simp at h
    simp [h]

theorem evalElem_lvalue_error (mem : Memory) (x y : Value)
                              (h : evalElem mem x y = .error .lvalue)
: (∃ x', x = .lvalue x') ∨ (∃ y', y = .lvalue y') := by
  unfold evalElem at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
    simp [h]
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
    simp [h]
  split at h <;> try simp at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h

theorem evalElemRef_lvalue_error (x y : Value)
                                 (h : evalElemRef x y = .error .lvalue)
: (∃ x', x = .lvalue x') ∨ (∃ y', y = .lvalue y') := by
  unfold evalElemRef at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
    simp [h]
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
    simp [h]
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
  split at h <;> simp at h
  . subst h
    rename_i h
    simp at h

theorem prepareCall_lvalue_error (mem : Memory) (x : Value) (xs : List RValue)
                                 (h : prepareCall mem x xs = .error .lvalue)
: ∃ x', x = .lvalue x' := by
  unfold prepareCall at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
    assumption
  split at h <;> try simp at h
  split at h <;> simp at h

theorem commitCall_lvalue_error (env : Environment) (mem : Memory) (x : Value)
                                (h : commitCall env mem x = .err .lvalue)
: ∃ x', x = .lvalue x' := by
  unfold commitCall at h
  split at h <;> simp at h
  clear h
  rename_i h
  simp at h
  assumption

theorem evalAssign_lvalue_error (st : State) (x y : Value)
                                (h : evalAssign st x y = .error .lvalue)
: (∃ x', x = .rvalue x') ∨ (∃ y', y = .lvalue y') := by
  unfold evalAssign at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
    simp [h]
  split at h <;> simp at h
  subst h
  rename_i h
  unfold evalAssignR at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
    simp [h]
  split at h <;> try simp at h
  . split at h <;> simp at h
    subst h
    rename_i h
    simp [Environment.assign_no_lvalue_error] at h
  . split at h <;> simp at h
    subst h
    rename_i h
    simp [BoxValue.assign_no_lvalue_error] at h

theorem chooseCase_lvalue_error (mem : Memory) (x : Value)
                                (bs : List (Pattern × Expr))
                                (h : chooseCase mem x bs = .error .lvalue)
: ∃ x', x = .lvalue x' := by
  unfold chooseCase at h
  simp [Bind.bind, Except.bind] at h
  split at h <;> simp at h
  subst h
  rename_i h
  simp at h
  assumption

theorem prepareDefList_names (ds : List Definition)
: ∀ x, x ∈ (prepareDefList ds).1 <-> x ∈ Definition.names ds := by
  fun_induction prepareDefList with
  | case1 => simp
  | case2 x y ds env e h₁ h₂ ih =>
    simp [h₁] at ih
    simp [ih]
    rw [<-ih]
    exact h₂
  | case3 x y ds env e h₁ h₂ ih =>
    simp [h₁] at ih
    simp [ih]
  | case4 x xs body ds env e h env' ih =>
    simp [h] at ih
    subst env'
    split_ifs with h'
    . simp [ih]
      rw [<-ih]
      exact h'
    simp [ih]

theorem Eval_no_lvalue_error (st : State) (e : Expr)
                             (r : Result Value) (cat : Category)
                             (h₂ : st.CategoryWF)
                             (h₃ : e.WF cat) (h₄ : Eval st e r)
: r ≠ .err .lvalue := by
  induction h₄
  using Eval.rec (motive_2 := fun st es r _ => st.CategoryWF → (∀ e ∈ es, e.WF .val) → r ≠ .err .lvalue)
  generalizing cat with
  | skip => simp
  | varOk => simp
  | varErr st x e h =>
    contrapose! h
    simp at h
    subst h
    apply evalVar_no_lvalue_error
  | refOk => simp
  | refErr st x e h =>
    contrapose! h
    simp at h
    subst h
    apply checkRef_no_some_lvalue
  | int => simp
  | str => simp
  | arrOk => simp
  | arrErr st xs e h ih =>
    cases h₃ with
    | arr _ h₃ =>
      specialize ih h₂ h₃
      contrapose! ih
      simp at ih
      subst ih
      simp
  | sexpOk => simp
  | sexpErr st t xs e h ih =>
    cases h₃ with
    | sexp _ _ h₃ =>
      specialize ih h₂ h₃
      contrapose! ih
      simp at ih
      subst ih
      simp
  | lambdaOk => simp
  | lambdaErr => simp
  | binopOk => simp
  | binopErr st₁ st₂ st₃ op x₁ x₂ y₁ y₂ e h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | binop _ _ _ h₃₁ h₃₂ =>
      have hwf₁ := Eval_category_wf _ _ _ _ .val h₂ h₃₁ h₄
      have hwf₂ := Eval_category_wf _ _ _ _ .val hwf₁.2 h₃₂ h₅
      simp at hwf₁ hwf₂
      obtain ⟨ ⟨ y₁, rfl ⟩, - ⟩ := hwf₁
      obtain ⟨ ⟨ y₂, rfl ⟩, - ⟩ := hwf₂
      intro h
      simp at h
      subst h
      apply evalBinop_lvalue_error at h₆
      simp at h₆
  | binopErrL st op x₁ x₂ e h ih =>
    cases h₃
    exact ih .val h₂ (by assumption)
  | binopErrR st st' op x₁ x₂ y₁ e h₄ h₅ ih₁ ih₂ =>
    apply ih₂ .val
    · exact (Eval_category_wf _ _ _ _ _ h₂ (by cases h₃; assumption) h₄).2
    · cases h₃
      assumption
  | elemOk => simp
  | elemErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | elem _ _ h₃₁ h₃₂ =>
      have hwf₁ := Eval_category_wf _ _ _ _ .val h₂ h₃₁ h₄
      have hwf₂ := Eval_category_wf _ _ _ _ .val hwf₁.2 h₃₂ h₅
      simp at hwf₁ hwf₂
      obtain ⟨ ⟨ y₁, rfl ⟩, - ⟩ := hwf₁
      obtain ⟨ ⟨ y₂, rfl ⟩, - ⟩ := hwf₂
      intro h
      simp at h
      subst h
      apply evalElem_lvalue_error at h₆
      simp at h₆
  | elemErrL st x₁ x₂ e h ih =>
    apply ih .val h₂
    cases h₃
    assumption
  | elemErrR st st' x₁ x₂ y₁ e h₄ h₅ ih₁ ih₂ =>
    apply ih₂ .val
    · exact (Eval_category_wf _ _ _ _ _ h₂ (by cases h₃; assumption) h₄).2
    · cases h₃
      assumption
  | elemRefOk => simp
  | elemRefErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | elemRef _ _ h₃₁ h₃₂ =>
      have hwf₁ := Eval_category_wf _ _ _ _ .val h₂ h₃₁ h₄
      have hwf₂ := Eval_category_wf _ _ _ _ .val hwf₁.2 h₃₂ h₅
      simp at hwf₁ hwf₂
      obtain ⟨ ⟨ y₁, rfl ⟩, - ⟩ := hwf₁
      obtain ⟨ ⟨ y₂, rfl ⟩, - ⟩ := hwf₂
      intro h
      simp at h
      subst h
      apply evalElemRef_lvalue_error at h₆
      simp at h₆
  | elemRefErrL st x₁ x₂ e h ih =>
    apply ih .val h₂
    cases h₃
    assumption
  | elemRefErrR st st' x₁ x₂ y₁ e h₄ h₅ ih₁ ih₂ =>
    apply ih₂ .val
    · exact (Eval_category_wf _ _ _ _ _ h₂ (by cases h₃; assumption) h₄).2
    · cases h₃
      assumption
  | callOk st₁ st₂ st₃ st₄ st₅ x xs y ys z z' h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    cases h₃ with
    | call _ _ h₃₁ h₃₂ =>
      have hwf₁ := Eval_category_wf _ _ _ _ .val h₂ h₃₁ h₄
      have hwf₂ := EvalList_category_wf _ _ _ _ hwf₁.2 h₃₂ h₅
      intro h
      apply commitCall_lvalue_error at h
      obtain ⟨ z', rfl ⟩ := h
      apply Eval_category_wf _ _ _ _ .val at h₇
      . simp at h₇
      . apply prepareCall_state_category_wf at h₆
        . assumption
        . exact hwf₂.mem
      . apply prepareCall_expr_wf at h₆
        . assumption
        . exact hwf₂.mem
  | callErr₁ st x xs e h ih =>
    cases h₃ with
    | call _ _ h₃ => exact ih .val h₂ h₃
  | callErr₂ st st' x xs y e h₄ h₅ ih₁ ih₂ =>
    cases h₃ with
    | call _ _ h₃₁ h₃₂ =>
      have hwf := Eval_category_wf _ _ _ _ _ h₂ h₃₁ h₄
      specialize ih₂ hwf.2 h₃₂
      contrapose ih₂
      simp at ih₂
      subst ih₂
      simp
  | callErr₃ st₁ st₂ st₃ x xs y ys e h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | call _ _ h₃₁ h₃₂ =>
      have hwf := Eval_category_wf _ _ _ _ _ h₂ h₃₁ h₄
      intro h
      simp at h
      subst h
      apply prepareCall_lvalue_error at h₆
      obtain ⟨ y, rfl ⟩ := h₆
      simp at hwf
  | callErr₄ st₁ st₂ st₃ st₄ x xs y ys z e h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    cases h₃ with
    | call _ _ h₃₁ h₃₂ =>
      have hwf₁ := Eval_category_wf _ _ _ _ _ h₂ h₃₁ h₄
      have hwf₂ := EvalList_category_wf _ _ _ _ hwf₁.2 h₃₂ h₅
      apply ih₃ .val
      . exact prepareCall_state_category_wf _ _ _ _ _ hwf₂.mem h₆
      . exact prepareCall_expr_wf _ _ _ _ _ hwf₂.mem h₆
  | assignOk => simp
  | assignErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | assign _ _ _ h₃₁ h₃₂ =>
      have hwf₁ := Eval_category_wf _ _ _ _ _ h₂ h₃₁ h₄
      have hwf₂ := Eval_category_wf _ _ _ _ .val hwf₁.2 h₃₂ h₅
      simp at hwf₁ hwf₂
      obtain ⟨ ⟨ y₁, rfl, - ⟩, - ⟩ := hwf₁
      obtain ⟨ ⟨ y₂, rfl ⟩, - ⟩ := hwf₂
      intro h
      simp at h
      subst h
      apply evalAssign_lvalue_error at h₆
      simp at h₆
  | assignErrL st x₁ x₂ e h ih =>
    cases h₃ with
    | assign _ _ _ h₃₁ h₃₂ => exact ih (.ref _) h₂ h₃₁
  | assignErrR st st' x₁ x₂ y₁ e h₄ h₅ ih₁ ih₂ =>
    cases h₃ with
    | assign _ _ _ h₃₁ h₃₂ =>
      apply ih₂ .val
      · exact (Eval_category_wf _ _ _ _ _ h₂ h₃₁ h₄).2
      · exact h₃₂
  | seqOk st₁ st₂ x₁ x₂ y₁ res h₄ h₅ ih₁ ih₂ =>
    cases h₃ with
    | seq _ catl catr _ hl hr =>
      apply ih₂
      . apply Eval_category_wf at h₄ <;> try assumption
        simp [h₄]
      . assumption
  | seqErr st x₁ x₂ e h ih =>
    cases h₃ with
    | seq _ _ _ _ hl hr => exact ih _ h₂ hl
  | iteThen st st' x₁ x₂ x₃ y₁ res h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | iteVal _ _ _ hc ht he =>
      exact ih₂ .val (Eval_category_wf _ _ _ _ _ h₂ hc h₄).2 ht
    | iteRef _ _ _ xs ys hc ht he =>
      exact ih₂ (.ref xs) (Eval_category_wf _ _ _ _ _ h₂ hc h₄).2 ht
  | iteElse st st' x₁ x₂ x₃ y₁ res h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | iteVal _ _ _ hc ht he =>
      exact ih₂ .val (Eval_category_wf _ _ _ _ _ h₂ hc h₄).2 he
    | iteRef _ _ _ xs ys hc ht he =>
      exact ih₂ (.ref ys) (Eval_category_wf _ _ _ _ _ h₂ hc h₄).2 he
  | iteErr₁ st x₁ x₂ x₃ e h ih =>
    cases h₃ with
    | iteVal _ _ _ hc ht he => exact ih .val h₂ hc
    | iteRef _ _ _ xs ys hc ht he => exact ih .val h₂ hc
  | iteErr₂ st st' x₁ x₂ x₃ y₁ e h₄ h₅ ih =>
    contrapose! h₅
    simp at h₅
    subst h₅
    apply Eval_category_wf _ _ _ _ .val at h₄
    . simp at h₄
      simp
      obtain ⟨ ⟨ y, rfl ⟩, - ⟩ := h₄
      simp
    . assumption
    . cases h₃ <;> assumption
  | loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    apply ih₃
    on_goal 2 => assumption
    cases h₃ with
    | loop _ _ cat h₃₁ h₃₂ =>
      apply Eval_category_wf _ _ _ _ cat at h₆
      on_goal 3 => assumption
      . simp [h₆]
      apply Eval_category_wf _ _ _ _ .val at h₄
      on_goal 3 => assumption
      . simp [h₄]
      . assumption
  | loopStop => simp
  | loopErr st st' x₁ x₂ y₁ e h₄ h₅ ih =>
    cases h₃ with
    | loop _ _ _ hc =>
      contrapose! h₅
      simp at h₅
      subst h₅
      simp
      apply Eval_category_wf _ _ _ _ .val at h₄
      on_goal 2 => assumption
      on_goal 2 => assumption
      simp at h₄
      obtain ⟨ ⟨ y, rfl ⟩, - ⟩ := h₄
      simp
  | loopErrL st x₁ x₂ e h ih =>
    cases h₃ with
    | loop _ _ _ hc => exact ih _ h₂ hc
  | loopErrR st st' x₁ x₂ y₁ e h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | loop _ _ _ hc hb =>
      exact ih₂ _ (Eval_category_wf _ _ _ _ _ h₂ hc h₄).2 hb
  | caseOk st st' x₁ bs y₁ xs x₂ res h₄ h₅ h₆ ih₁ ih₂ =>
    apply Eval_category_wf _ _ _ _ .val at h₄
    on_goal 2 => assumption
    on_goal 2 => cases h₃ <;> assumption
    have hwf₁ : (st'.pushEnv xs).CategoryWF := by
      simp [State.CategoryWF_iff, h₄.2.mem, h₄.2.env]
      apply chooseCase_env_category_wf at h₅
      assumption
    cases h₃ with
    | caseVal _ _ _ h₃ =>
      have hwf₂ := chooseCase_expr_wf_val _ _ _ _ _ h₃ h₅
      specialize ih₂ .val hwf₁ hwf₂
      contrapose! ih₂
      apply Result.popEnv_lvalue_error at ih₂
      obtain ih₂ | ⟨ xs₁, env', x, st₁, rfl, ih₁, ih₂ ⟩ := ih₂
      . assumption
      apply Eval_category_wf _ _ _ _ .val at h₆
      . simp at h₆
      . assumption
      . assumption
    | caseRef _ _ xs' _ _ h₃₁ h₃₂ =>
      obtain ⟨ i, hwf₂, hwf₃ ⟩ := chooseCase_expr_wf_ref _ _ _ _ _ xs' h₃₁ h₅
      specialize ih₂ (.ref xs'[i]) hwf₁ hwf₂
      contrapose! ih₂
      apply Result.popEnv_lvalue_error at ih₂
      obtain ih₂ | ⟨ xs₁, env', x, st₁, rfl, ih₁, ih₂ ⟩ := ih₂
      . assumption
      have := (Eval_state_monotonic _ _ _ _ h₆).env
      simp [ih₁] at this
      replace this := SimpleEnv.SameShape_mem _ _ this.1
      rw [<-this, hwf₃] at ih₂
      apply Eval_category_wf _ _ _ _ (.ref xs'[i]) at h₆ <;> try assumption
      simp at h₆
      obtain ⟨ h₆, - ⟩ := h₆
      specialize h₃₂ i
      specialize @h₃₂ {x}
      simp at h₃₂
      nomatch h₃₂ h₆ ih₂
  | caseErr₁ st x₁ bs e h ih =>
    apply ih
    . assumption
    . cases h₃ <;> assumption
  | caseErr₂ st st' x₁ bs y₁ e h₄ h₅ ih =>
    apply Eval_category_wf _ _ _ _ .val at h₄
    on_goal 2 => assumption
    on_goal 2 => cases h₃ <;> assumption
    intro h
    simp at h
    subst h
    apply chooseCase_lvalue_error at h₅
    obtain ⟨ y₁, rfl ⟩ := h₅
    simp at h₄
  | scope st x₁ env x₂ res h₄ h₅ ih =>
    have hwf₁ : (st.pushEnv env).CategoryWF := by
      simp [State.CategoryWF_iff, h₂.mem, h₂.env]
      apply prepareDefList_env_category_wf at h₄
      . assumption
      cases h₃ <;> assumption
    have hwf₂ : (x₂.seq x₁.body).WF cat := by
      constructor
      . apply prepareDefList_expr_wf at h₄
        . assumption
        cases h₃ <;> assumption
      . cases h₃ <;> assumption
    specialize ih cat hwf₁ hwf₂
    contrapose! ih
    apply Result.popEnv_lvalue_error at ih
    obtain ih | ⟨ xs₁, env', x, st', rfl, ih₁, ih₂ ⟩ := ih
    . assumption
    have hwf₃ := Eval_category_wf _ _ _ _ cat hwf₁ hwf₂ h₅
    simp at hwf₃
    obtain ⟨ ⟨ xs₂, rfl, hwf₃ ⟩, - ⟩ := hwf₃
    cases h₃ with
    | scopeRef ds e _ _ h₃₁ h₃₂ =>
      have := (Eval_state_monotonic _ _ _ _ h₅).env
      simp [ih₁] at this
      replace this := SimpleEnv.SameShape_mem _ _ this.1
      rw [<-this] at ih₂
      replace this := prepareDefList_names ds
      simp [h₄] at this
      rw [this] at ih₂
      specialize @h₃₂ {x}
      simp [hwf₃, ih₂] at h₃₂
  | nil => simp
  | cons => simp
  | err st st' x xs y h ih h₁ h₂ =>
    apply Eval_category_wf at h
    on_goal 3 => assumption
    on_goal 3 =>
      apply h₂
      simp
    simp at h
  | errL st x xs e h ih h₁ h₂ =>
    specialize ih _ h₁ (h₂ _ ?_)
    . simp
    contrapose! ih
    simp at ih
    subst ih
    simp
  | errR st st' x xs y e h₃ h₄ ih₁ ih₂ h₁ h₂ =>
    apply ih₂
    on_goal 2 =>
      intro e he
      apply h₂
      simp [he]
    apply Eval_category_wf _ _ _ _ .val at h₃
    . simp [h₃]
    . assumption
    . apply h₂
      simp
