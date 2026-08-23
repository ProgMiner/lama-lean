import Mathlib


import Lama.Semantics.WellFormed

namespace Lama.Semantics

open Lama.Ast

@[simp]
theorem RValue.toNat?_metatheory_error (x : RValue)
: x.toNat? ≠ .error .metatheory := by
  unfold toNat?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem BoxValue.assign_metatheory_error (i : ℕ) (x : RValue) (v : BoxValue)
: v.assign i x = .error .metatheory <-> v = .undefined := by
  unfold assign
  cases v <;> simp
  . simp [Bind.bind, Except.bind, Functor.map, Except.map]
    split <;> try simp
    . rename_i h
      simp at h
      obtain ⟨ h, rfl ⟩ := h
      simp
    split <;> try simp
    . rename_i h
      simp at h
      obtain ⟨ h, rfl ⟩ := h
      simp
    split <;> simp
    rename_i h
    simp at h
    obtain ⟨ _, rfl ⟩ := h
    simp
  . simp [Functor.map, Except.map]
    split <;> simp
    rename_i h
    simp at h
    obtain ⟨ h, rfl ⟩ := h
    simp
  . simp [Functor.map, Except.map]
    split <;> simp
    rename_i h
    simp at h
    obtain ⟨ h, rfl ⟩ := h
    simp

theorem Environment.lookup_metatheory_error (env : Environment)
                                            (x : Ident) (mem : Memory)
                                            (h : env.lookup x mem = .error .metatheory)
: ¬ env.WF mem := by
  fun_induction lookup with
  | case1 => simp at h
  | case2 =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    rename_i h
    subst h
    simp at h
  | case3 b h' =>
    simp at h'
    simp [h']
  | case4 => simp at h
  | case5 xs env h' ih =>
    apply ih at h
    simp [h]

theorem Environment.assign_metatheory_error (x : Ident) (y : RValue)
                                            (mem : Memory) (env : Environment)
                                            (h : env.assign x y mem = .error .metatheory)
: ∀ z, env.lookup x mem ≠ .ok (.var z) := by
  fun_induction Environment.assign with
  | case1 => simp
  | case2 => simp at h
  | case3 b xs params body h₁ h₂ =>
    simp [h₁, Functor.map, Except.map]
    split <;> simp
    rename_i y' h
    simp at h
    simp [h] at h₂
    intro z
    unfold EnvValue.toLookup
    cases y' <;> simp at *
  | case4 => simp
  | case5 => simp at h
  | case6 xs env params body h' => simp [h']
  | case7 xs env h' ih =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    subst h
    rename_i h
    apply ih at h
    simp [h']
    exact h

theorem Environment.close_none (env : Environment) (mem : Memory)
                               (h : env.close mem = .none)
: ¬ env.WF mem := by
  fun_induction close with
  | case1 => simp at h
  | case2 => simp at h
  | case3 b h' =>
    simp at h'
    simp [h']
  | case4 xs env ih =>
    simp at h
    simp
    intro
    apply ih
    simp [Option.eq_none_iff_forall_ne_some, h]

@[simp]
theorem Environment.pop_none (env : Environment)
: env.pop = .none <-> ∀ xs env', env ≠ .scope xs env' := by
  unfold pop
  split <;> simp

@[simp]
theorem State.popEnv_none (st : State)
: st.popEnv = .none <-> st.env.pop = .none := by
  unfold popEnv
  simp [<-Option.eq_none_iff_forall_ne_some]

@[simp]
theorem Value.toInt?_metatheory_error (x : Value)
: x.toInt? ≠ .error .metatheory := by
  unfold toInt?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem Value.toNat?_metatheory_error (x : Value)
: x.toNat? ≠ .error .metatheory := by
  unfold toNat?
  simp [Bind.bind, Except.bind]
  split
  . rename_i h
    simp at h
    obtain ⟨ h, rfl ⟩ := h
    simp
  rename_i h
  simp at h
  subst x
  simp

@[simp]
theorem Value.toBool?_metatheory_error (x : Value)
: x.toBool? ≠ .error .metatheory := by
  unfold toBool?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem Value.toBox?_metatheory_error (x : Value)
: x.toBox? ≠ Except.error Error.metatheory := by
  unfold toBox?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

theorem Result.popEnv_metatheory_error (r : Result Value)
                                       (h : r.popEnv = .err .metatheory)
: r = .err .metatheory ∨ ∃ x st, r = .ok x st ∧ st.popEnv = .none := by
  unfold popEnv at h
  split at h
  on_goal 2 => simp [h]
  rename_i x st
  simp
  extract_lets at h
  rename_i ok
  clear_value ok
  split_ifs at h <;> simp at h
  split at h <;> simp at h
  rename_i h'
  simp at h'
  assumption

theorem evalVar_metatheory_error (st : State) (x : Ident)
                                 (h : evalVar st x = .error .metatheory)
: ¬ st.WF := by
  unfold evalVar at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h
  case h_1 e h =>
    simp at h
    subst e
    apply Environment.lookup_metatheory_error at h
    simp [State.WF_iff, h]
  split at h <;> try simp at h
  split at h <;> try simp at h
  subst h
  rename_i h₁ _ h₂
  apply Environment.lookup_wf at h₁
  simp at h₁ h₂
  apply Environment.close_none at h₂
  intro h₃
  apply h₂
  apply h₁
  . exact h₃.mem
  . exact h₃.env

theorem checkRef_some_metatheory (st : State) (x : Ident)
                                 (h : checkRef st x = .some .metatheory)
: ¬ st.env.WF st.mem := by
  unfold checkRef at h
  split at h <;> simp at h
  rename_i e h
  subst e
  simp at h
  apply Environment.lookup_metatheory_error at h
  assumption

theorem evalBinop_metatheory_error (x y : Value) (op : Binop)
: evalBinop x y op ≠ .error .metatheory := by
  unfold evalBinop
  cases op
  all_goals simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  all_goals split <;> try simp
  all_goals try split <;> try simp
  all_goals intro rfl
  all_goals try simp at *

theorem evalElem_metatheory_error (st : State) (x y : Value)
                                  (h : evalElem st.mem x y = .error .metatheory)
: ¬ (x.WF st ∧ st.mem.WF) := by
  unfold evalElem at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
  rename_i b hb
  simp at hb
  subst x
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
  split at h <;> try simp at h
  . clear h
    rename_i h
    intro ⟨ h₁, h₂ ⟩
    replace h₂ := h₂.bound b
    simp only [h, gt_iff_lt, true_iff] at h₂
    apply h₂
    exact h₁
  split at h <;> try simp at h
  subst h
  rename_i h
  simp at h

theorem evalAssign_metatheory_error (st : State) (x y : Value)
                                    (h : evalAssign st x y = .error .metatheory)
: ¬ (st.WF ∧ x.WF st) := by
  unfold evalAssign at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
  rename_i y h'
  simp at h'
  subst h'
  split at h <;> simp at h
  subst h
  rename_i h
  unfold evalAssignR at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  . subst h
    rename_i h
    simp at h
  rename_i x h'
  simp at h'
  subst h'
  simp
  cases x with
  | var x =>
    simp at h
    split at h <;> simp at h
    subst h
    rename_i h
    apply Environment.assign_metatheory_error at h
    simp [h]
  | elem b i =>
    simp at h
    split at h <;> simp at h
    subst h
    rename_i h
    simp at h
    intro h'
    replace h' := h'.mem.bound b
    simp [h] at h'
    simp [h']

theorem Eval_no_metatheory_error (st : State) (e : Expr) (r : Result Value)
                                 (h₁ : st.WF) (h₂ : Eval st e r)
: r ≠ .err .metatheory := by
  induction h₂
  using Eval.rec (motive_2 := fun st es r _ => st.WF -> r ≠ .err .metatheory)
  with
  | skip => simp
  | varOk => simp
  | varErr st x e h₂ =>
    contrapose! h₁
    simp at h₁
    subst e
    apply evalVar_metatheory_error at h₂
    apply h₂
  | refOk => simp
  | refErr st x e h₂ =>
    contrapose! h₁
    simp at h₁
    subst e
    apply checkRef_some_metatheory at h₂
    simp [State.WF_iff, h₂]
  | int => simp
  | str => simp
  | arrOk => simp
  | arrErr st xs e h₂ ih =>
    specialize ih h₁
    contrapose! ih
    simp at ih
    simp [ih]
  | sexpOk => simp
  | sexpErr st t xs e h₂ ih =>
    specialize ih h₁
    contrapose! ih
    simp at ih
    simp [ih]
  | lambdaOk => simp
  | lambdaErr st xs x h₂ =>
    apply Environment.close_none at h₂
    simp [State.WF_iff, h₂] at h₁
  | binopOk => simp
  | binopErr st₁ st₂ st₃ op x₁ x₂ y₁ y₂ e h₂ h₃ h₄ =>
    contrapose! h₄
    simp at h₄
    subst e
    apply evalBinop_metatheory_error
  | binopErrL st op x₁ x₂ e h ih =>
    apply ih
    assumption
  | binopErrR st st' op x₁ x₂ y₁ e h₂ h₃ ih₁ ih₂ =>
    apply ih₂
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    simp [h₂]
  | elemOk => simp
  | elemErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₂ h₃ h₄ ih₁ ih₂ =>
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    intro h
    simp at h
    subst e
    apply evalElem_metatheory_error at h₄
    apply h₄
    clear h₄
    and_intros
    . apply Value.WF_transport
      on_goal 3 => exact h₂.1
      . exact h₂.2
      apply Eval_state_monotonic
      . assumption
    . apply Eval_result_wf at h₃
      on_goal 2 => exact h₂.2
      simp at h₃
      exact h₃.2.mem
  | elemErrL st x₁ x₂ e h ih =>
    apply ih
    assumption
  | elemErrR st st' x₁ x₂ y₁ e h₂ h₃ ih₁ ih₂ =>
    apply ih₂
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    simp [h₂]
  | elemRefOk => simp
  | elemRefErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₂ h₃ h₄ ih₁ ih₂ =>
    contrapose! h₄
    simp at h₄
    subst e
    unfold evalElemRef
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
    split <;> try simp
    . rename_i h
      simp at h
      obtain ⟨ h, rfl ⟩ := h
      simp
    split <;> try simp
    . rename_i h
      simp at h
      obtain ⟨ h, rfl ⟩ := h
      simp
    split <;> try simp
    . rename_i h
      simp at h
      obtain ⟨ h, rfl ⟩ := h
      simp
    split <;> try simp
    rename_i h
    contrapose! h
    subst h
    simp
  | elemRefErrL st x₁ x₂ e h ih =>
    apply ih
    assumption
  | elemRefErrR st st' x₁ x₂ y₁ e h₂ h₃ ih₁ ih₂ =>
    apply ih₂
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    simp [h₂]
  | callOk =>
    unfold commitCall
    split <;> simp
  | callErr₁ st x xs e h ih =>
    apply ih
    assumption
  | callErr₂ st st' x xs y e h₂ h₃ ih₁ ih₂ =>
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    specialize ih₂ h₂.2
    contrapose! ih₂
    simp at ih₂
    subst e
    simp
  | callErr₃ st₁ st₂ st₃ x xs y ys e h₂ h₃ h₄ ih₁ ih₂ =>
    contrapose! h₄
    simp at h₄
    subst e
    unfold prepareCall
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
    split <;> try simp
    . rename_i h
      contrapose! h
      subst h
      simp
    split <;> try simp
    split <;> try simp
  | callErr₄ st₁ st₂ st₃ st₄ x xs y ys z e h₂ h₃ h₄ h₅ ih₁ ih₂ ih₃ =>
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    apply EvalList_result_wf at h₃
    on_goal 2 => exact h₂.2
    simp at h₃
    apply prepareCall_state_wf at h₄
    on_goal 2 => exact h₃.2.mem
    on_goal 2 => exact h₃.1
    apply ih₃
    assumption
  | assignOk => simp
  | assignErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₂ h₃ h₄ ih₁ ih₂ =>
    suffices st₃.WF ∧ y₁.WF st₃ by
      contrapose this
      simp at this
      subst e
      apply evalAssign_metatheory_error at h₄
      assumption
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    and_intros
    . apply Eval_result_wf at h₃
      on_goal 2 => exact h₂.2
      exact h₃.2
    . apply Eval_state_monotonic at h₃
      apply Value.WF_transport
      . exact h₂.2
      . assumption
      . exact h₂.1
  | assignErrL st x₁ x₂ e h ih =>
    apply ih
    assumption
  | assignErrR st st' x₁ x₂ y₁ e h₂ h₃ ih₁ ih₂ =>
    apply ih₂
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    simp [h₂]
  | seqOk st₁ st₂ x₁ x₂ y₁ res h₂ h₃ ih₁ ih₂ =>
    apply ih₂
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    simp [h₂]
  | seqErr st x₁ x₂ e h ih =>
    apply ih
    assumption
  | iteThen st st' x₁ x₂ x₃ y₁ res h₂ h₃ h₄ ih₁ ih₂ =>
    apply ih₂
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    simp [h₂]
  | iteElse st st' x₁ x₂ x₃ y₁ res h₂ h₃ h₄ ih₁ ih₂ =>
    apply ih₂
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    simp [h₂]
  | iteErr₁ st x₁ x₂ x₃ e h ih =>
    apply ih
    assumption
  | iteErr₂ st st' x₁ x₂ x₃ y₁ e h₂ h₃ ih =>
    contrapose! h₃
    simp at h₃
    subst e
    simp
  | loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res h₂ h₃ h₄ h₅ ih₁ ih₂ ih₃ =>
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    apply Eval_result_wf at h₄
    on_goal 2 => exact h₂.2
    simp at h₄
    apply ih₃
    exact h₄.2
  | loopStop => simp
  | loopErr st st' x₁ x₂ y₁ e h₂ h₃ ih =>
    contrapose! h₃
    simp at h₃
    subst e
    simp
  | loopErrL st x₁ x₂ e h ih =>
    apply ih
    assumption
  | loopErrR st st' x₁ x₂ y₁ e h₂ h₃ h₄ ih₁ ih₂ =>
    apply ih₂
    apply Eval_result_wf at h₂
    on_goal 2 => assumption
    simp at h₂
    simp [h₂]
  | caseOk st st' x₁ bs y₁ env x₂ res h₂ h₃ h₄ ih₁ ih₂ =>
    intro h
    apply Result.popEnv_metatheory_error at h
    obtain h | ⟨ x, st', rfl, h ⟩ := h
    . subst h
      apply Eval_result_wf at h₂
      on_goal 2 => assumption
      simp at h₂
      simp at ih₂
      apply ih₂
      simp [State.WF_iff, h₂.2.mem, h₂.2.env]
      apply chooseCase_env_wf at h₃
      apply h₃
      . exact h₂.2.mem
      . exact h₂.1
    simp at h
    apply Eval_state_monotonic at h₄
    replace h₄ := h₄.env
    unfold Environment.SameShape at h₄
    split at h₄ <;> simp at *
    rename_i h' _
    exact h _ _ h'
  | caseErr₁ st x₁ bs e h ih =>
    apply ih
    assumption
  | caseErr₂ st st' x₁ bs y₁ e h₂ h₃ ih =>
    contrapose! h₃
    simp at h₃
    subst e
    unfold chooseCase
    simp [Bind.bind, Except.bind]
    split <;> simp
    rename_i h
    simp at h
    obtain ⟨ h, rfl ⟩ := h
    simp
  | scope st x₁ env s₂ res h₂ h₃ ih =>
    intro h
    apply Result.popEnv_metatheory_error at h
    obtain h | ⟨ x, st', rfl, h ⟩ := h
    . subst h
      simp at ih
      apply ih
      simp [State.WF_iff, h₁.mem, h₁.env]
      apply prepareDefList_env_wf at h₂
      assumption
    simp at h
    apply Eval_state_monotonic at h₃
    replace h₃ := h₃.env
    unfold Environment.SameShape at h₃
    split at h₃ <;> simp at *
    rename_i h' _
    exact h _ _ h'
  | nil => simp
  | cons => simp
  | err => simp
  | errL st x xs e h₁ ih h₂ =>
    specialize ih h₂
    contrapose! ih
    simp at ih
    subst e
    simp
  | errR st st' x xs y e h₁ h₂ ih₁ ih₂ r₂ =>
    apply ih₂
    apply Eval_result_wf at h₁
    on_goal 2 => assumption
    simp at h₁
    simp [h₁]
