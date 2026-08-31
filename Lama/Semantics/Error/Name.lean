import Lama.Semantics.Closed


namespace Lama.Semantics

open Ast

@[simp]
theorem RValue.toNat?_no_name_error (x : RValue)
: x.toNat? ≠ .error .name := by
  unfold toNat?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem ClosedEnv.lookup_context (x : Ident) (env : ClosedEnv)
: env.context.lookup x = (env.lookup x).map EnvLookup.isVar := by
  fun_induction lookup with
  | case1 => simp
  | case2 xs env y h => simp [h]
  | case3 xs env h ih =>
    simp [<- ih]
    rw [Finmap.lookup_union_right]
    simp [Finmap.mem_iff, h]

@[simp]
theorem BoxValue.assign_no_name_error (i : ℕ) (x : RValue) (v : BoxValue)
: v.assign i x ≠ .error .name := by
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
    contrapose! h
    subst h
    simp
  . simp [Functor.map, Except.map]
    split <;> try simp
    rename_i h
    contrapose! h
    subst h
    simp
  . simp [Functor.map, Except.map]
    split <;> try simp
    rename_i h
    contrapose! h
    subst h
    simp

theorem Environment.lookup_name_error (mem : Memory) (x : Ident) (env : Environment)
                                      (h : env.lookup x mem = .error .name)
: x ∉ env.context mem := by
  fun_induction lookup with
  | case1 => simp
  | case2 box env params body h' =>
    simp at h
    simp [h', Finmap.mem_iff, h]
  | case3 => simp at h
  | case4 xs env y h' =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    subst h
    rename_i h
    simp at h
  | case5 xs env h' ih =>
    apply ih at h
    simp [h]
    simp [Finmap.mem_iff, h']

theorem Environment.lookup_ok_context (mem : Memory) (x : Ident)
                                      (env : Environment) (y : EnvLookup)
                                      (h : env x mem = .ok y)
: (env.context mem).lookup x = .some y.isVar := by
  simp at h
  fun_induction lookup with
  | case1 => simp at h
  | case2 box env params body h' =>
    simp at h
    simp [h', h]
  | case3 => simp at h
  | case4 xs env y h' =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    subst h
    rename_i h
    simp [h']
  | case5 xs env h' ih =>
    simp [h] at ih
    simp [h', ih]
    simp [Finmap.mem_iff, h']

theorem Environment.assign_no_name_error (x : Ident) (y : RValue)
                                         (mem : Memory) (env : Environment)
: env.assign x y mem ≠ .error .name := by
  fun_induction assign with
  | case1 => simp
  | case2 box env params body h =>
    simp [Functor.map, Except.map]
    split <;> simp
    rename_i h'
    simp at h'
    obtain ⟨ h', rfl ⟩ := h'
    simp
  | case3 => simp
  | case4 => simp
  | case5 => simp
  | case6 xs env h ih =>
    simp [Functor.map, Except.map]
    split <;> simp
    rename_i h'
    rw [h'] at ih
    contrapose! ih
    subst ih
    simp

@[simp]
theorem Value.toInt?_no_name_error (x : Value)
: x.toInt? ≠ .error .name := by
  unfold toInt?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem Value.toNat?_no_name_error (x : Value)
: x.toNat? ≠ .error .name := by
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
theorem Value.toBool?_no_name_error (x : Value)
: x.toBool? ≠ .error .name := by
  unfold toBool?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

@[simp]
theorem Value.toBox?_no_name_error (x : Value)
: x.toBox? ≠ Except.error Error.name := by
  unfold toBox?
  simp [Bind.bind, Except.bind]
  split <;> simp
  rename_i h
  simp at h
  obtain ⟨ h, rfl ⟩ := h
  simp

theorem evalVar_name_error (st : State) (x : Ident)
                           (h : evalVar st x = Except.error Error.name)
: x ∉ st.context := by
  unfold evalVar at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h
  on_goal 2 => split at h <;> simp at h
  simp at h
  subst h
  rename_i h
  apply Environment.lookup_name_error at h
  exact h

theorem checkRef_some_name (st : State) (x : Ident)
                           (h : checkRef st x = .some .name)
: st.context.lookup x ≠ .some true := by
  unfold checkRef at h
  simp at h
  split at h <;> simp at h
  . clear h
    rename_i y h₁ h₂
    contrapose! h₁
    apply Environment.lookup_ok_context at h₂
    rw [h₁] at h₂
    simp at h₂
    cases y <;> simp at *
  . subst h
    rename_i h
    apply Environment.lookup_name_error at h
    rw [Finmap.mem_iff] at h
    contrapose! h
    simp [h]

theorem evalBinop_no_name_error (x y : Value) (op : Binop)
: evalBinop x y op ≠ .error .name := by
  unfold evalBinop
  cases op
  all_goals simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  all_goals split <;> try simp
  all_goals try split <;> try simp
  all_goals intro rfl
  all_goals try simp at *

theorem evalElem_no_name_error (mem : Memory) (x y : Value)
: evalElem mem x y ≠ .error .name := by
  unfold evalElem
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    simp
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    simp
  split <;> try simp
  split <;> try simp
  rename_i h
  contrapose! h
  subst h
  simp

theorem evalElemRef_no_name_error (x y : Value)
: evalElemRef x y ≠ .error .name := by
  unfold evalElemRef
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    simp
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    simp
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    simp
  split <;> try simp
  rename_i h
  contrapose! h
  subst h
  simp

theorem prepareCall_no_name_error (mem : Memory) (x : Value) (xs : List RValue)
: prepareCall mem x xs ≠ .error .name := by
  unfold prepareCall
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    simp
  split <;> try simp
  split_ifs <;> simp

theorem evalAssign_no_name_error (st : State) (x y : Value)
: evalAssign st x y ≠ .error .name := by
  unfold evalAssign
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    simp
  split <;> try simp
  rename_i h
  contrapose! h
  subst h
  rename_i y hy _
  simp at hy
  subst hy
  unfold evalAssignR
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure]
  split <;> try simp
  . rename_i h
    contrapose! h
    subst h
    simp
  split <;> try simp
  . split <;> try simp
    rename_i h
    contrapose! h
    subst h
    apply Environment.assign_no_name_error
  . split <;> try simp
    rename_i h
    contrapose! h
    subst h
    apply BoxValue.assign_no_name_error

theorem Eval_no_name_error (st : State) (e : Expr) (r : Result Value)
                           (h₁ : st.WF) (h₂ : st.IsClosed)
                           (h₃ : e.IsClosed st.context)
                           (h₄ : Eval st e r)
: r ≠ .err .name := by
  induction h₄
  using Eval.rec (motive_2 := fun st es r _ => st.WF -> st.IsClosed -> (∀ e ∈ es, e.IsClosed st.context) -> r ≠ .err .name)
  with
  | skip => simp
  | varOk => simp
  | varErr st x e h =>
    simp at *
    contrapose! h₃
    subst e
    apply evalVar_name_error at h
    exact h
  | refOk => simp
  | refErr st x e h =>
    intro h
    simp at h
    subst h
    apply checkRef_some_name at h
    apply h
    exact h₃
  | int => simp
  | str => simp
  | arrOk => simp
  | arrErr st xs e h ih =>
    simp at h₃
    specialize ih h₁ h₂ h₃
    contrapose ih
    simp at ih
    subst e
    simp
  | sexpOk => simp
  | sexpErr st t xs e h ih =>
    simp at h₃
    specialize ih h₁ h₂ h₃
    contrapose ih
    simp at ih
    subst e
    simp
  | lambdaOk => simp
  | lambdaErr => simp
  | binopOk => simp
  | binopErr st₁ st₂ st₃ op x₁ x₂ y₁ y₂ e h₄ h₄ h₆ ih₁ ih₂ =>
    contrapose! h₆
    simp at h₆
    subst e
    apply evalBinop_no_name_error
  | binopErrL st op x₁ x₂ e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | binopErrR st st' op x₁ x₂ y₁ e h₄ h₅ ih₁ ih₂ =>
    apply ih₂
    . apply Eval_result_wf at h₄
      . exact h₄.2
      . assumption
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    obtain ⟨ -, h₃ ⟩ := h₃
    rw [State.context_transport] at h₃
    . assumption
    . assumption
    apply Eval_state_monotonic at h₄
    assumption
  | elemOk => simp
  | elemErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₄ h₅ h₆ ih₁ ih₂ =>
    contrapose! h₆
    simp at h₆
    subst e
    apply evalElem_no_name_error
  | elemErrL st x₁ x₂ e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | elemErrR st st' x₁ x₂ y₁ e h₄ h₅ ih₁ ih₂ =>
    apply ih₂
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    . simp at h₃
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . assumption
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
  | elemRefOk => simp
  | elemRefErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₄ h₅ h₆ ih₁ ih₂ =>
    contrapose! h₆
    simp at h₆
    subst e
    apply evalElemRef_no_name_error
  | elemRefErrL st x₁ x₂ e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | elemRefErrR st st' x₁ x₂ y₁ e h₄ h₅ ih₁ ih₂ =>
    apply ih₂
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    . simp at h₃
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . assumption
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
  | callOk =>
    unfold commitCall
    split <;> simp
  | callErr₁ st x xs e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | callErr₂ st st' x xs y e h₄ h₅ ih₁ ih₂ =>
    have hwf : st'.WF := by
      apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    specialize ih₂ hwf ?_ ?_
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    . obtain ⟨ -, h₃ ⟩ := h₃
      simp at h₃
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    contrapose! ih₂
    simp at ih₂
    subst e
    simp
  | callErr₃ st₁ st₂ st₃ x xs y ys e h₄ h₅ h₆ ih₁ ih₂ =>
    contrapose! h₆
    simp at h₆
    subst e
    apply prepareCall_no_name_error
  | callErr₄ st₁ st₂ st₃ st₄ x xs y ys z e h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    have hwf₁ := Eval_result_wf _ _ _ ?_ h₄
    on_goal 2 => assumption
    simp at hwf₁
    have hwf₂ := EvalList_result_wf _ _ _ ?_ h₅
    on_goal 2 => simp [hwf₁]
    simp at hwf₂
    simp at h₃
    have hcl : st₃.IsClosed := by
      apply EvalList_state_closed at h₅
      . assumption
      . simp [hwf₁]
      . apply Eval_state_closed at h₄
        . assumption
        . assumption
        . assumption
        . simp [h₃]
      . rw [<- State.context_transport]
        . exact h₃.2
        . assumption
        apply Eval_state_monotonic at h₄
        assumption
    apply ih₃
    . apply prepareCall_state_wf at h₆
      . assumption
      . exact hwf₂.2.mem
      . exact hwf₂.1
    . simp [State.IsClosed_iff, <- prepareCall_memory _ _ _ _ _ h₆, hcl.mem]
      apply prepareCall_env_closed at h₆
      assumption
    . apply prepareCall_expr_closed at h₆
      . assumption
      . exact hcl.mem
  | assignOk => simp
  | assignErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₄ h₅ h₆ ih₁ ih₂ =>
    contrapose! h₆
    simp at h₆
    subst e
    apply evalAssign_no_name_error
  | assignErrL st x₁ x₂ e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | assignErrR st st' x₁ x₂ y₁ e h₄ h₅ ih₁ ih₂ =>
    apply ih₂
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    . simp at h₃
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . assumption
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
  | seqOk st₁ st₂ x₁ x₂ y₁ res h₄ h₅ ih₁ ih₂ =>
    apply ih₂
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    . simp at h₃
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . assumption
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
  | seqErr st x₁ x₂ e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | iteThen st st' x₁ x₂ x₃ y₁ res h₄ h₅ h₆ ih₁ ih₂ =>
    apply ih₂
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    . simp at h₃
      obtain ⟨ -, h₃, - ⟩ := h₃
      rw [State.context_transport] at h₃
      . assumption
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
  | iteElse st st' x₁ x₂ x₃ y₁ res h₄ h₅ h₆ ih₁ ih₂ =>
    apply ih₂
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    . simp at h₃
      obtain ⟨ -, -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . assumption
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
  | iteErr₁ st x₁ x₂ x₃ e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | iteErr₂ st st' x₁ x₂ x₃ y₁ e h₄ h₅ ih =>
    contrapose! h₅
    simp at h₅
    subst e
    simp
  | loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    have hwf₂ : st₂.WF := by
      apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    have hwf₃ : st₃.WF := by
      apply Eval_result_wf at h₆
      on_goal 2 => assumption
      simp at h₆
      exact h₆.2
    apply ih₃
    . assumption
    . apply Eval_state_closed at h₆
      . assumption
      . assumption
      . apply Eval_state_closed at h₄
        . assumption
        . assumption
        . assumption
        . exact h₃.1
      . obtain ⟨ -, h₃ ⟩ := h₃
        rw [State.context_transport] at h₃
        . exact h₃
        . assumption
        apply Eval_state_monotonic at h₄
        assumption
    rw [State.context_transport] at h₃
    . exact h₃
    . assumption
    apply Eval_state_monotonic at h₄
    apply Eval_state_monotonic at h₆
    grw [h₄, h₆]
  | loopStop => simp
  | loopErr st st' x₁ x₂ y₁ e h₄ h₅ ih =>
    contrapose! h₅
    simp at h₅
    subst e
    simp
  | loopErrL st x₁ x₂ e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | loopErrR st st' x₁ x₂ y₁ e h₄ h₅ h₆ ih₁ ih₂ =>
    apply ih₂
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      simp at h₄
      exact h₄.2
    . apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . exact h₃.1
    . obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . assumption
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
  | caseOk st st' x₁ bs y₁ xs x₂ res h₄ h₅ h₆ ih₁ ih₂ =>
    contrapose! ih₂
    unfold Result.popEnv at ih₂
    cases res <;> simp at ih₂
    . split_ifs at ih₂ <;> try simp at ih₂
      split at ih₂ <;> simp at ih₂
    subst ih₂
    have hwf := Eval_result_wf _ _ _ ?_ h₄
    on_goal 2 => assumption
    simp at hwf
    have hcl := Eval_state_closed _ _ _ _ ?_ ?_ ?_ h₄ <;> try simp [*]
    simp at h₃
    simp [State.WF_iff, State.IsClosed_iff, hwf.2.mem, hwf.2.env]
    and_intros
    . apply chooseCase_env_wf at h₅
      apply h₅
      . exact hwf.2.mem
      . exact hwf.1
    . exact hcl.mem
    . apply chooseCase_env_closed at h₅
      assumption
    . exact hcl.env
    . apply chooseCase_expr_closed at h₅
      . assumption
      simp
      apply Eval_state_monotonic at h₄
      rw [<- Environment.context_transport]
      . exact h₃.2
      . exact h₁.mem
      . exact h₁.env
      . exact h₄.mem
      . exact h₄.env
  | caseErr₁ st x₁ bs e h ih =>
    simp at h₃
    apply ih
    . assumption
    . assumption
    . simp [h₃]
  | caseErr₂ st st' x₁ bs y₁ e h₃ h₄ ih =>
    contrapose! h₄
    simp at h₄
    subst e
    unfold chooseCase
    simp [Bind.bind, Except.bind]
    split <;> simp
    rename_i h
    simp at h
    obtain ⟨ h, rfl ⟩ := h
    simp
  | scope st x₁ env x₂ res h₄ h₅ ih =>
    obtain ⟨ ds, x₁ ⟩ := x₁
    simp at h₃ h₄ h₅ ih
    contrapose! ih
    unfold Result.popEnv at ih
    cases res <;> simp at ih
    . split_ifs at ih <;> try simp at ih
      split at ih <;> simp at ih
    subst ih
    rw [prepareDefList_env_context (h := h₄)] at h₃
    simp [State.WF_iff, State.IsClosed_iff, h₁.mem, h₁.env, h₂.mem, h₂.env, h₃.1]
    and_intros
    . apply prepareDefList_env_wf at h₄
      assumption
    . apply prepareDefList_env_closed at h₄
      . assumption
      . exact h₃.2
    . apply prepareDefList_expr_closed' at h₄
      . assumption
      . exact h₃.2
  | nil => simp
  | cons => simp
  | err => simp
  | errL st x xs e h₁ ih h₂ h₃ h₄ =>
    intro h
    simp at h
    subst e
    apply ih
    on_goal 4 => simp
    . assumption
    . assumption
    apply h₄
    simp
  | errR st st' x xs y e h₁ h₂ ih₁ ih₂ h₃ h₄ h₅ =>
    apply ih₂
    . apply Eval_result_wf at h₁
      on_goal 2 => assumption
      simp at h₁
      exact h₁.2
    . apply Eval_state_closed at h₁
      . assumption
      . assumption
      . assumption
      . apply h₅
        simp
    intro e' he'
    rw [State.context_transport] at h₅
    . apply h₅
      simp [he']
    . assumption
    apply Eval_state_monotonic at h₁
    assumption
