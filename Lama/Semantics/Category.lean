import Lama.Ast.WellFormed
import Lama.Semantics.Closed


namespace Lama.Semantics

open Ast

def EnvValue.CategoryWF : EnvValue -> Prop
| .var _ => True
| .fn _ body => body.WF .val

@[simp]
theorem EnvValue.CategoryWF_var (x : RValue)
: (.var x : EnvValue).CategoryWF := by trivial

@[simp]
theorem EnvValue.CategoryWF_fn (xs : List Ident) (body : Expr)
: (.fn xs body : EnvValue).CategoryWF ↔ body.WF .val := by rfl

def SimpleEnv.CategoryWF (env : SimpleEnv) : Prop :=
  ∀ x y, env.lookup x = .some y -> y.CategoryWF

def ClosedEnv.CategoryWF : ClosedEnv -> Prop
| .empty => True
| .scope xs parent => xs.CategoryWF ∧ parent.CategoryWF

@[simp]
theorem ClosedEnv.empty_category_wf
: (∅ : ClosedEnv).CategoryWF := by trivial

@[simp]
theorem ClosedEnv.scope_category_wf (xs : SimpleEnv) (parent : ClosedEnv)
: (ClosedEnv.scope xs parent).CategoryWF <-> xs.CategoryWF ∧ parent.CategoryWF := by rfl

def EnvLookup.CategoryWF : EnvLookup -> Prop
| .var _ => True
| .fn env _ body => env.CategoryWF ∧ body.WF .val

@[simp]
theorem EnvLookup.CategoryWF_var (x : RValue)
: (.var x : EnvLookup).CategoryWF := by trivial

@[simp]
theorem EnvLookup.CategoryWF_fn (env : ClosedEnv) (xs : List Ident) (body : Expr)
: (.fn env xs body : EnvLookup).CategoryWF <-> env.CategoryWF ∧ body.WF .val := by rfl

theorem EnvValue.toLookup_category_wf (env : ClosedEnv) (x : EnvValue)
                                      (h₁ : env.CategoryWF) (h₂ : x.CategoryWF)
: (x.toLookup env).CategoryWF := by
  cases x with
  | var => trivial
  | fn params body => exact ⟨ h₁, h₂ ⟩

theorem ClosedEnv.lookup_category_wf (env : ClosedEnv) (x : Ident) (res : EnvLookup)
                                     (h₁ : env.lookup x = .some res) (h₂ : env.CategoryWF)
: res.CategoryWF := by
  induction env with
  | empty => simp at h₁
  | scope xs parent ih =>
    simp at h₁ h₂
    split at h₁
    · rename_i y hy
      cases h₁
      apply EnvValue.toLookup_category_wf
      . simp [*]
      apply h₂.1
      assumption
    · apply ih
      · exact h₁
      · exact h₂.2

theorem ClosedEnv.assign_category_wf (env env' : ClosedEnv)
                                     (x : Ident) (y : RValue)
                                     (h₁ : env.CategoryWF)
                                     (h₂ : env.assign x y = .some env')
: env'.CategoryWF := by
  fun_induction assign generalizing env' with
  | case1 => simp at h₂
  | case2 xs env y' h =>
    simp at h₁ h₂
    subst h₂
    simp [h₁]
    intro x' y' hy'
    by_cases hx' : x' = x
    . subst x'
      simp at hy'
      subst hy'
      simp
    simp [hx'] at hy'
    apply h₁.1
    assumption
  | case3 => simp at h₂
  | case4 xs env h ih =>
    simp [Option.bind] at h₂
    split at h₂ <;> simp at h₂
    subst h₂
    rename_i env' h
    simp at h₁
    simp [h₁]
    simp [h] at ih
    apply ih
    simp [h₁]

def BoxValue.CategoryWF : BoxValue -> Prop
| .undefined => True
| .str _ => True
| .arr _ => True
| .sexp _ _ => True
| .closure env _ body => env.CategoryWF ∧ body.WF .val

@[simp]
theorem BoxValue.CategoryWF_undefined
: (.undefined : BoxValue).CategoryWF := by trivial

@[simp]
theorem BoxValue.CategoryWF_str (xs : ByteArray)
: (.str xs : BoxValue).CategoryWF := by trivial

@[simp]
theorem BoxValue.CategoryWF_arr (xs : List RValue)
: (.arr xs : BoxValue).CategoryWF := by trivial

@[simp]
theorem BoxValue.CategoryWF_sexp (t : Tag) (xs : List RValue)
: (.sexp t xs : BoxValue).CategoryWF := by trivial

@[simp]
theorem BoxValue.CategoryWF_closure (env : ClosedEnv) (xs : List Ident) (body : Expr)
: (.closure env xs body : BoxValue).CategoryWF <-> env.CategoryWF ∧ body.WF .val := by rfl

theorem BoxValue.assign_category_wf (x z : BoxValue) (i : ℕ) (y : RValue)
                                    (h : x.assign i y = .ok z)
: z.CategoryWF := by
  cases x with
  | undefined => simp at h
  | str xs =>
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> simp at h
    subst h
    simp
  | arr xs =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    subst h
    simp
  | sexp t xs =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    subst h
    simp
  | closure => simp at h

def Memory.CategoryWF (mem : Memory) : Prop :=
  ∀ b, (mem b).CategoryWF

@[simp]
theorem Memory.empty_category_wf
: (∅ : Memory).CategoryWF := by
  intro b
  change (.undefined : BoxValue).CategoryWF
  simp

theorem Memory.alloc_category_wf (mem mem' : Memory) (x : Box)
                                 (h₁ : mem.CategoryWF)
                                 (h₂ : mem.alloc = (x, mem'))
: mem'.CategoryWF := by
  simp at h₂
  obtain ⟨ rfl, rfl ⟩ := h₂
  exact h₁

theorem Memory.assign_category_wf (mem : Memory) (x : Box) (y : BoxValue)
                                  (h₁ : mem.CategoryWF) (h₂ : y.CategoryWF)
: (mem.assign x y).CategoryWF := by
  simp [CategoryWF]
  intro b
  split_ifs with hb
  . assumption
  . apply h₁

theorem Memory.allocWith_category_wf (mem mem' : Memory) (x : BoxValue) (y : Box)
                                     (h₁ : mem.CategoryWF) (h₂ : x.CategoryWF)
                                     (h₃ : mem.allocWith x = (y, mem'))
: mem'.CategoryWF := by
  unfold allocWith at h₃
  split at h₃
  obtain ⟨ rfl, rfl ⟩ := h₃
  rename_i mem' h₃
  apply assign_category_wf
  on_goal 2 => assumption
  apply alloc_category_wf at h₃ <;> assumption

def Environment.CategoryWF
: Environment -> Prop
| .empty => True
| .closure _ => True
| .scope xs env => xs.CategoryWF ∧ env.CategoryWF

@[simp]
theorem Environment.CategoryWF_empty
: CategoryWF .empty := True.intro

@[simp]
theorem Environment.CategoryWF_closure (b : Box)
: CategoryWF (.closure b) := True.intro

@[simp]
theorem Environment.CategoryWF_scope (xs : SimpleEnv) (env : Environment)
: CategoryWF (.scope xs env) <-> xs.CategoryWF ∧ env.CategoryWF := by rfl

@[simp]
theorem Environment.empty_category_wf
: (∅ : Environment).CategoryWF := by
  simp [CategoryWF]

theorem Environment.close_category_wf (mem : Memory)
                                      (env : Environment)
                                      (env' : ClosedEnv)
                                      (h₁ : mem.CategoryWF)
                                      (h₂ : env.CategoryWF)
                                      (h₃ : env.close mem = .some env')
: env'.CategoryWF := by
  fun_induction env.close mem generalizing env' with
  | case1 =>
    simp at h₃
    subst h₃
    simp
  | case2 b env params body h =>
    simp at h₃
    subst h₃
    specialize h₁ b
    simp [h] at h₁
    simp [h₁]
  | case3 => simp at h₃
  | case4 xs env ih =>
    simp [Option.bind] at h₃
    split at h₃ <;> simp at h₃
    subst h₃
    rename_i env' h
    simp [h] at ih
    simp at h₂ ⊢
    simp [h₂] at ih ⊢
    assumption

theorem Environment.lookup_category_wf (mem : Memory) (env : Environment)
                                       (x : Ident) (y : EnvLookup)
                                       (h₁ : mem.CategoryWF)
                                       (h₂ : env.CategoryWF)
                                       (h₃ : env x mem = .ok y)
: y.CategoryWF := by
  simp at h₃
  fun_induction env.lookup x mem with
  | case1 => simp at h₃
  | case2 b env params body h =>
    simp at h₃
    apply ClosedEnv.lookup_category_wf at h₃
    apply h₃
    specialize h₁ b
    simp [h] at h₁
    simp [h₁]
  | case3 => simp at h₃
  | case4 xs env y h =>
    simp [Functor.map, Except.map] at h₃
    split at h₃ <;> simp at h₃
    subst h₃
    rename_i env' h'
    simp [Option.bind] at h'
    split at h' <;> simp at h'
    subst h'
    rename_i env' h'
    apply EnvValue.toLookup_category_wf
    on_goal 2 =>
      apply h₂.1
      assumption
    simp at h₂
    apply close_category_wf at h'
    . simp [h₂, h']
    . assumption
    . simp [h₂]
  | case5 xs env h ih =>
    simp [h₃] at ih
    apply ih
    exact h₂.2

theorem Environment.assign_memory_category_wf (mem mem' : Memory)
                                              (env env' : Environment)
                                              (x : Ident) (y : RValue)
                                              (h₁ : mem.CategoryWF)
                                              (h₂ : env.assign x y mem = .ok (env', mem'))
: mem'.CategoryWF := by
  fun_induction assign generalizing env' with
  | case1 => simp at h₂
  | case2 b env params body h =>
    simp [Functor.map, Except.map] at h₂
    split at h₂ <;> simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    rename_i env' h'
    simp at h'
    apply Memory.assign_category_wf
    . assumption
    simp
    specialize h₁ b
    simp [h] at h₁
    and_intros
    on_goal 2 => simp [h₁]
    apply ClosedEnv.assign_category_wf at h'
    . assumption
    specialize h₁
    simp [h₁]
  | case3 => simp at h₂
  | case4 xs env y' h =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    assumption
  | case5 => simp at h₂
  | case6 xs env h ih =>
    simp [Functor.map, Except.map] at h₂
    split at h₂ <;> simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    rename_i res h'
    simp [h'] at ih
    apply ih
    rfl

theorem Environment.assign_env_category_wf (mem mem' : Memory)
                                           (env env' : Environment)
                                           (x : Ident) (y : RValue)
                                           (h₁ : env.CategoryWF)
                                           (h₂ : env.assign x y mem = .ok (env', mem'))
: env'.CategoryWF := by
  fun_induction assign generalizing env' with
  | case1 => simp at h₂
  | case2 b env params body h =>
    simp [Functor.map, Except.map] at h₂
    split at h₂ <;> simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    assumption
  | case3 => simp at h₂
  | case4 xs env y' h =>
    simp at h₁ h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    simp [h₁]
    intro x' y' hy'
    by_cases hx' : x' = x
    . subst x'
      simp at hy'
      subst hy'
      simp
    simp [hx'] at hy'
    apply h₁.1
    assumption
  | case5 => simp at h₂
  | case6 xs env h ih =>
    simp [Functor.map, Except.map] at h₂
    split at h₂ <;> simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    rename_i res h'
    simp at h₁
    simp [h₁]
    simp [h'] at ih
    apply ih
    . simp [h₁]
    . rfl

structure State.CategoryWF (st : State) : Prop where
  mem : st.mem.CategoryWF
  env : st.env.CategoryWF

theorem State.CategoryWF_iff (st : State)
: st.CategoryWF <-> st.mem.CategoryWF ∧ st.env.CategoryWF where
  mp h := by
    obtain ⟨ h₁, h₂ ⟩ := h
    exact ⟨ h₁, h₂ ⟩
  mpr h := by
    obtain ⟨ h₁, h₂ ⟩ := h
    exact ⟨ h₁, h₂ ⟩

@[simp]
theorem State.empty_category_wf
: (State.empty : State).CategoryWF := by
  simp [State.CategoryWF_iff]

theorem State.allocWith_category_wf (st st' : State) (x : BoxValue) (y : Box)
                                    (h₁ : st.CategoryWF) (h₂ : x.CategoryWF)
                                    (h₃ : st.allocWith x = (y, st'))
: st'.CategoryWF := by
  unfold allocWith at h₃
  split at h₃
  obtain ⟨ rfl, rfl ⟩ := h₃
  rename_i mem h₃
  simp [CategoryWF_iff, h₁.env]
  apply Memory.allocWith_category_wf at h₃
  . assumption
  . exact h₁.mem
  . assumption

def LValue.HasCategory (xs : Finset Ident)
: LValue -> Prop
| .var x => x ∈ xs
| .elem _ _ => True

@[simp]
theorem LValue.HasCategory_var (x : Ident) (xs : Finset Ident)
: HasCategory xs (.var x) <-> x ∈ xs := by rfl

@[simp]
theorem LValue.HasCategory_elem (b : Box) (i : ℕ) (xs : Finset Ident)
: HasCategory xs (.elem b i) := True.intro

theorem LValue.HasCategory_transport (xs xs' : Finset Ident) (x : LValue)
                                     (h₁ : xs ⊆ xs') (h₂ : x.HasCategory xs)
: x.HasCategory xs' := by
  cases x with
  | elem => simp
  | var x =>
    simp at *
    exact h₁ h₂

def Value.HasCategory : Value -> Category -> Prop
| .rvalue _, .val => True
| .lvalue x, .ref xs => x.HasCategory xs
| _, _ => False

@[simp]
theorem Value.HasCategory_val (x : Value)
: x.HasCategory .val <-> ∃ y, x = .rvalue y := by
  cases x <;> simp [Value.HasCategory]

@[simp]
theorem Value.HasCategory_ref (x : Value) (xs : Finset Ident)
: x.HasCategory (.ref xs) <-> ∃ y, x = .lvalue y ∧ y.HasCategory xs := by
  cases x <;> simp [Value.HasCategory]

@[simp]
theorem Value.HasCategory_rvalue (x : RValue) (cat : Category)
: (Value.rvalue x).HasCategory cat <-> cat = .val := by
  cases cat <;> simp

@[simp]
theorem Value.HasCategory_lvalue (x : LValue) (cat : Category)
: (Value.lvalue x).HasCategory cat <-> ∃ xs, cat = .ref xs ∧ x.HasCategory xs := by
  cases cat <;> simp

theorem evalVar_category_wf (st st' : State)
                            (x : Ident) (y : RValue)
                            (h₁ : st.CategoryWF)
                            (h₂ : evalVar st x = .ok (y, st'))
: st'.CategoryWF := by
  unfold evalVar at h₂
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₂
  split at h₂ <;> try simp at h₂
  split at h₂ <;> simp at h₂
  all_goals obtain ⟨ rfl, rfl ⟩ := h₂
  . assumption
  rename_i env params body h
  change (st.allocWith (.closure env params body)).2.CategoryWF
  apply State.allocWith_category_wf st _  (h₃ := rfl)
  . assumption
  apply Environment.lookup_category_wf at h
  . exact h
  . exact h₁.mem
  . exact h₁.env

theorem prepareCall_state_category_wf (mem : Memory) (st : State) (body : Expr)
                                      (x : Value) (xs : List RValue)
                                      (h₁ : mem.CategoryWF)
                                      (h₂ : prepareCall mem x xs = .ok (st, body))
: st.CategoryWF := by
  unfold prepareCall at h₂
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₂
  split at h₂ <;> try simp at h₂
  rename_i b hb
  simp at hb
  subst hb
  split at h₂ <;> try simp at h₂
  rename_i env params body h
  split_ifs at h₂
  simp at h₂
  obtain ⟨ rfl, rfl ⟩ := h₂
  simp [State.CategoryWF_iff, h₁]
  change (prepareCallEnv _ _).CategoryWF
  intro x' y' hy'
  apply prepareCallEnv_incl at hy'
  simp at hy'
  obtain ⟨ y', rfl, - ⟩ := hy'
  simp

theorem prepareCall_expr_wf (mem : Memory) (st : State) (body : Expr)
                            (x : Value) (xs : List RValue)
                            (h₁ : mem.CategoryWF)
                            (h₂ : prepareCall mem x xs = .ok (st, body))
: body.WF .val := by
  unfold prepareCall at h₂
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₂
  split at h₂ <;> try simp at h₂
  rename_i b hb
  simp at hb
  subst hb
  split at h₂ <;> try simp at h₂
  rename_i env params body h
  split_ifs at h₂
  simp at h₂
  obtain ⟨ rfl, rfl ⟩ := h₂
  specialize h₁ b
  simp [h] at h₁
  simp [h₁]

theorem evalAssign_category_wf (st st' : State)
                               (x y : Value) (z : RValue)
                               (h₁ : st.CategoryWF)
                               (h₂ : evalAssign st x y = .ok (st', z))
: st'.CategoryWF := by
  unfold evalAssign at h₂
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₂
  split at h₂ <;> try simp at h₂
  rename_i y hy
  simp at hy
  subst hy
  split at h₂ <;> simp at h₂
  obtain ⟨ rfl, rfl ⟩ := h₂
  rename_i st' h₂
  unfold evalAssignR at h₂
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₂
  split at h₂ <;> try simp at h₂
  rename_i x hx
  simp at hx
  subst hx
  cases x with
  | var x =>
    simp at h₂
    split at h₂ <;> simp at h₂
    subst h₂
    rename_i res h
    obtain ⟨ env, mem ⟩ := res
    simp [State.CategoryWF_iff]
    and_intros
    . apply Environment.assign_memory_category_wf at h
      . assumption
      . exact h₁.mem
    . apply Environment.assign_env_category_wf at h
      . assumption
      . exact h₁.env
  | elem b i =>
    simp at h₂
    split at h₂ <;> simp at h₂
    subst h₂
    rename_i z hz
    simp [State.CategoryWF_iff, h₁.env]
    apply Memory.assign_category_wf
    . exact h₁.mem
    apply BoxValue.assign_category_wf at hz
    assumption

theorem evalPattern_category_wf (mem : Memory) (x : RValue)
                                (p : Pattern) (env : SimpleEnv)
                                (h : evalPattern mem x p = .some env)
: env.CategoryWF := by
  induction p
  using Pattern.rec (motive_2 := fun ps => ∀ xs env, evalPatternList mem xs ps = .some env -> env.CategoryWF)
  generalizing x env with
  | wildcard =>
    simp at h
    subst h
    simp [SimpleEnv.CategoryWF]
  | const =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp [SimpleEnv.CategoryWF]
  | string =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp [SimpleEnv.CategoryWF]
  | array ps ih =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> try simp at h
    specialize ih _ _ h
    assumption
  | sexp t ps ih =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> try simp at h
    obtain ⟨ rfl, h ⟩ := h
    specialize ih _ _ h
    assumption
  | named n p ih =>
    simp [Option.bind] at h
    split at h <;> simp at h
    subst h
    rename_i env h
    specialize ih _ _ h
    intro x' y' hy'
    by_cases hx' : x' = n
    . subst x'
      simp at hy'
      subst hy'
      simp
    simp [hx'] at hy'
    apply ih
    assumption
  | boxTag =>
    simp at h
    split at h <;> simp at h
    subst h
    simp [SimpleEnv.CategoryWF]
  | valTag =>
    simp at h
    split at h <;> simp at h
    subst h
    simp [SimpleEnv.CategoryWF]
  | strTag =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    subst h
    simp [SimpleEnv.CategoryWF]
  | arrayTag =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    subst h
    simp [SimpleEnv.CategoryWF]
  | sexpTag =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    subst h
    simp [SimpleEnv.CategoryWF]
  | funTag =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    subst h
    simp [SimpleEnv.CategoryWF]
  | nil xs env h =>
    cases xs <;> simp at h
    subst h
    simp [SimpleEnv.CategoryWF]
  | cons p ps ih₁ ih₂ xs env h =>
    cases xs <;> simp at h
    simp [Option.bind] at h
    split at h <;> simp at h
    rename_i env₁ h₁
    split at h <;> simp at h
    rename_i env₂ h₂
    subst h
    specialize ih₁ _ _ h₁
    specialize ih₂ _ _ h₂
    intro x' y' hy'
    simp at hy'
    obtain hy' | ⟨ -, hy' ⟩ := hy'
    . apply ih₂
      assumption
    . apply ih₁
      assumption

theorem chooseCaseR_env_category_wf (mem : Memory) (x : RValue)
                                    (bs : List (Pattern × Expr))
                                    (env : SimpleEnv) (e : Expr)
                                    (h : chooseCaseR mem x bs = .some (env, e))
: env.CategoryWF := by
  fun_induction chooseCaseR with
  | case1 => simp at h
  | case2 p e bs env h =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    apply evalPattern_category_wf at h
    assumption
  | case3 p e bs h ih =>
    simp [h] at ih
    assumption

theorem chooseCase_env_category_wf (mem : Memory) (x : Value)
                                   (bs : List (Pattern × Expr))
                                   (env : SimpleEnv) (e : Expr)
                                   (h : chooseCase mem x bs = .ok (env, e))
: env.CategoryWF := by
  unfold chooseCase at h
  simp [Bind.bind, Except.bind] at h
  split at h <;> simp at h
  rename_i x hx
  simp at hx
  subst hx
  apply chooseCaseR_env_category_wf at h
  assumption

theorem chooseCaseR_expr_wf_val (mem : Memory) (x : RValue)
                                (bs : List (Pattern × Expr))
                                (env : SimpleEnv) (e : Expr)
                                (h₁ : ∀ b ∈ bs, b.2.WF .val)
                                (h₂ : chooseCaseR mem x bs = .some (env, e))
: e.WF .val := by
  fun_induction chooseCaseR with
  | case1 => simp at h₂
  | case2 p e bs env h =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    apply h₁ (p, e)
    simp
  | case3 p e bs h ih =>
    simp [h₂] at ih
    apply ih
    intro p b h
    apply h₁ (p, b)
    simp [h]

theorem chooseCase_expr_wf_val (mem : Memory) (x : Value)
                               (bs : List (Pattern × Expr))
                               (env : SimpleEnv) (e : Expr)
                               (h₁ : ∀ b ∈ bs, b.2.WF .val)
                               (h₂ : chooseCase mem x bs = .ok (env, e))
: e.WF .val := by
  unfold chooseCase at h₂
  simp [Bind.bind, Except.bind] at h₂
  split at h₂ <;> simp at h₂
  rename_i x hx
  simp at hx
  subst hx
  apply chooseCaseR_expr_wf_val at h₂ <;> assumption

theorem chooseCaseR_expr_wf_ref (mem : Memory) (x : RValue)
                                (bs : List (Pattern × Expr))
                                (env : SimpleEnv) (e : Expr)
                                (xs : List.Vector (Finset Ident) bs.length)
                                (h₁ : ∀ i : Fin bs.length, bs[i].2.WF (Category.ref (xs.get i)))
                                (h₂ : chooseCaseR mem x bs = .some (env, e))
: ∃ i : Fin bs.length, e.WF (.ref xs[i]) ∧ ∀ x, x ∈ env <-> x ∈ bs[i].1.vars := by
  fun_induction chooseCaseR with
  | case1 => simp at h₂
  | case2 p e bs env h =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    use ⟨ 0, by simp ⟩
    simp
    and_intros
    . apply h₁ ⟨ 0, by simp ⟩
    . apply evalPattern_context ∅ at h
      simp at h
      intro x'
      apply_fun (x' ∈ ·) at h
      simp at h
      simp [h, Finmap.mem_iff]
  | case3 p e bs h ih =>
    simp [h₂] at ih
    specialize ih xs.tail ?_
    . intro i
      specialize h₁ i.succ
      simp at h₁
      convert h₁ using 2
      simp
    obtain ⟨ i, ih ⟩ := ih
    use i.succ
    convert ih
    cases xs
    using List.Vector.casesOn
    rfl

theorem chooseCase_expr_wf_ref (mem : Memory) (x : Value)
                               (bs : List (Pattern × Expr))
                               (env : SimpleEnv) (e : Expr)
                               (xs : List.Vector (Finset Ident) bs.length)
                               (h₁ : ∀ i : Fin bs.length, bs[i].2.WF (Category.ref (xs.get i)))
                               (h₂ : chooseCase mem x bs = .ok (env, e))
: ∃ i : Fin bs.length, e.WF (.ref xs[i]) ∧ ∀ x, x ∈ env <-> x ∈ bs[i].1.vars := by
  unfold chooseCase at h₂
  simp [Bind.bind, Except.bind] at h₂
  split at h₂ <;> simp at h₂
  rename_i x hx
  simp at hx
  subst hx
  apply chooseCaseR_expr_wf_ref at h₂ <;> assumption

theorem prepareDefList_env_category_wf (ds : List Definition)
                                       (env : SimpleEnv) (e : Expr)
                                       (h₁ : ∀ d ∈ ds, d.WF)
                                       (h₂ : prepareDefList ds = (env, e))
: env.CategoryWF := by
  fun_induction prepareDefList generalizing env e with
  | case1 =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    simp [SimpleEnv.CategoryWF]
  | case2 x y ds env e h₂ h₃ ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    simp [h₂] at ih
    apply ih
    intro d hd
    apply h₁
    simp [hd]
  | case3 x y ds env e h₂ h₃ ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    simp [h₂] at ih
    specialize ih ?_
    . intro d hd
      apply h₁
      simp [hd]
    intro x' y' hy'
    by_cases hx' : x' = x
    . subst x'
      simp at hy'
      subst y'
      simp
    simp [hx'] at hy'
    apply ih
    assumption
  | case4 x xs body ds env e h₂ env' ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    subst env'
    simp [h₂] at ih
    specialize ih ?_
    . intro d hd
      apply h₁
      simp [hd]
    split_ifs with h
    . apply ih
    intro x' y' hy'
    by_cases hx' : x' = x
    . subst x'
      simp at hy'
      subst y'
      specialize h₁ (.fn x xs body)
      simp at h₁
      cases h₁ with
      | fn _ _ _ h₁ => simp [h₁]
    simp [hx'] at hy'
    apply ih
    assumption

theorem prepareDefList_expr_wf (ds : List Definition)
                               (env : SimpleEnv) (e : Expr)
                               (h₁ : ∀ d ∈ ds, d.WF)
                               (h₂ : prepareDefList ds = (env, e))
: e.WF .val := by
  fun_induction prepareDefList generalizing env e with
  | case1 =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    constructor
  | case2 x y ds env e h₂ h₃ ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    simp [h₂] at ih
    constructor
    . specialize h₁ (.var x y)
      simp at h₁
      cases h₁ with
      | var' _ _ h₁ => exact h₁
    . apply ih
      intro d hd
      apply h₁
      simp [hd]
  | case3 x y ds env e h₂ h₃ ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    simp [h₂] at ih
    constructor
    . constructor
      . constructor
      specialize h₁ (.var x y)
      simp at h₁
      cases h₁ with
      | var' _ _ h₁ => exact h₁
    . apply ih
      intro d hd
      apply h₁
      simp [hd]
  | case4 x xs body ds env e h₂ env' ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    simp [h₂] at ih
    apply ih
    intro d hd
    apply h₁
    simp [hd]

theorem Eval_category_wf (st st' : State) (e : Expr)
                         (x : Value) (cat : Category)
                         (h₂ : st.CategoryWF) (h₃ : e.WF cat)
                         (h₄ : Eval st e (.ok x st'))
: x.HasCategory cat ∧ st'.CategoryWF := by
  generalize hr : Result.ok x st' = r at h₄
  symm at hr
  induction h₄
  using Eval.rec (motive_2 := fun st es r _ => st.CategoryWF -> (∀ e ∈ es, e.WF .val)
                                            -> ∀ xs st', r = .ok xs st' -> st'.CategoryWF)
  generalizing cat x st' with
  | skip =>
    cases h₃
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp [h₂]
  | varOk st st' x y h =>
    cases h₃
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp
    apply evalVar_category_wf at h <;> assumption
  | varErr => simp at hr
  | refOk st x h =>
    cases h₃
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp [h₂]
  | refErr => simp at hr
  | int =>
    cases h₃
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp [h₂]
  | str st st' s box h =>
    cases h₃
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply State.allocWith_category_wf at h
    . exact ⟨by simp, h⟩
    . exact h₂
    . simp
  | arrOk st₁ st₂ st₃ xs ys box h₄ h₅ ih =>
    cases h₃ with
    | arr _ h₃₁ =>
      simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      specialize ih h₂ h₃₁
      simp at ih ⊢
      apply State.allocWith_category_wf at h₅
      . exact h₅
      . exact ih
      . simp
  | arrErr => simp at hr
  | sexpOk st₁ st₂ st₃ t xs ys box h₄ h₅ ih =>
    cases h₃ with
    | sexp _ _ h₃₁ =>
      simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      specialize ih h₂ h₃₁
      simp at ih ⊢
      apply State.allocWith_category_wf at h₅
      . exact h₅
      . exact ih
      . simp
  | sexpErr => simp at hr
  | lambdaOk st st' xs x box env h₄ h₅ =>
    cases h₃ with
    | lambda _ _ h₃₁ =>
      simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      apply Environment.close_category_wf at h₄
      on_goal 2 => exact h₂.mem
      on_goal 2 => exact h₂.env
      apply State.allocWith_category_wf at h₅
      . simp [h₅]
      . assumption
      . simp [h₄, h₃₁]
  | lambdaErr => simp at hr
  | binopOk st₁ st₂ st₃ op x₁ x₂ y₁ y₂ z h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | binop op' l r h₃₁ h₃₂ =>
      simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      specialize ih₁ _ _ .val h₂ h₃₁ rfl
      specialize ih₂ _ _ .val ih₁.2 h₃₂ rfl
      simp [ih₂.2]
  | binopErr => simp at hr
  | binopErrL => simp at hr
  | binopErrR => simp at hr
  | elemOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | elem _ _ h₃₁ h₃₂ =>
      simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      specialize ih₁ _ _ .val h₂ h₃₁ rfl
      specialize ih₂ _ _ .val ih₁.2 h₃₂ rfl
      simp [ih₂]
  | elemErr => simp at hr
  | elemErrL => simp at hr
  | elemErrR => simp at hr
  | elemRefOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | elemRef _ _ h₃₁ h₃₂ =>
      simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      specialize ih₁ _ _ .val h₂ h₃₁ rfl
      specialize ih₂ _ _ .val ih₁.2 h₃₂ rfl
      simp [Value.HasCategory]
      apply evalElemRef_ok at h₆
      obtain ⟨ b, i, rfl, rfl, rfl ⟩ := h₆
      simp
      exact ih₂.2
  | elemRefErr => simp at hr
  | elemRefErrL => simp at hr
  | elemRefErrR => simp at hr
  | callOk st₁ st₂ st₃ st₄ st₅ x xs y ys z z' h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    cases h₃ with
    | call _ _ h₃₁ h₃₂ =>
      unfold commitCall at hr
      split at hr <;> simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      rename_i z' hz'
      simp at hz'
      subst hz'
      specialize ih₁ _ _ _ h₂ h₃₁ rfl
      specialize ih₂ ih₁.2 h₃₂ _ _ rfl
      have hcwf := prepareCall_state_category_wf _ _ _ _ _ ih₂.mem h₆
      have hwf := prepareCall_expr_wf _ _ _ _ _ ih₂.mem h₆
      specialize ih₃ _ _ _ hcwf hwf rfl
      simp [State.CategoryWF_iff, ih₃.2.mem, ih₂.env]
  | callErr₁ => simp at hr
  | callErr₂ => simp at hr
  | callErr₃ => simp at hr
  | callErr₄ => simp at hr
  | assignOk st₁ st₂ st₃ st₄ x₁ x₂ y₁ y₂ z h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | assign _ _ _ h₃₁ h₃₂ =>
      simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      specialize ih₁ _ _ (.ref _) h₂ h₃₁ rfl
      specialize ih₂ _ _ .val ih₁.2 h₃₂ rfl
      simp at ih₁ ih₂ ⊢
      apply evalAssign_category_wf at h₆
      . assumption
      . simp [ih₂]
  | assignErr => simp at hr
  | assignErrL => simp at hr
  | assignErrR => simp at hr
  | seqOk st₁ st₂ x₁ x₂ y₁ res h₄ h₅ ih₁ ih₂ =>
    cases h₃ with
    | seq _ _ cat₁ cat₂ h₃₁ h₃₂ =>
      subst res
      simp at ih₁ ih₂
      specialize ih₁ _ _ cat₁ h₂ h₃₁ rfl rfl
      exact ih₂ _ _ cat ih₁.2 h₃₂ rfl rfl
  | seqErr => simp at hr
  | iteThen st st' x₁ x₂ x₃ y₁ res h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | iteVal _ _ _ h₃₁ h₃₂ h₃₃ =>
      subst res
      simp at ih₁ ih₂
      specialize ih₁ _ _ .val h₂ h₃₁ rfl rfl
      exact ih₂ _ _ .val ih₁.2 h₃₂ rfl rfl
    | iteRef _ _ _ xs ys h₃₁ h₃₂ h₃₃ =>
      subst res
      simp at ih₁ ih₂
      specialize ih₁ _ _ .val h₂ h₃₁ rfl rfl
      specialize ih₂ _ _ (.ref xs) ih₁.2 h₃₂ rfl rfl
      simp only [ih₂.2, and_true]
      simp at ih₂
      obtain ⟨ ⟨ y₂, rfl, ih₂ ⟩, - ⟩ := ih₂
      simp
      apply LValue.HasCategory_transport (h₂ := ih₂)
      simp
  | iteElse st st' x₁ x₂ x₃ y₁ res h₄ h₅ h₆ ih₁ ih₂ =>
    cases h₃ with
    | iteVal _ _ _ h₃₁ h₃₂ h₃₃ =>
      subst res
      simp at ih₁ ih₂
      specialize ih₁ _ _ .val h₂ h₃₁ rfl rfl
      exact ih₂ _ _ .val ih₁.2 h₃₃ rfl rfl
    | iteRef _ _ _ xs ys h₃₁ h₃₂ h₃₃ =>
      subst res
      simp at ih₁ ih₂
      specialize ih₁ _ _ .val h₂ h₃₁ rfl rfl
      specialize ih₂ _ _ (.ref ys) ih₁.2 h₃₃ rfl rfl
      simp only [ih₂.2, and_true]
      simp at ih₂
      obtain ⟨ ⟨ y₂, rfl, ih₂ ⟩, - ⟩ := ih₂
      simp
      apply LValue.HasCategory_transport (h₂ := ih₂)
      simp
  | iteErr₁ => simp at hr
  | iteErr₂ => simp at hr
  | loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    cases h₃ with
    | loop _ _ cat' h₃₁ h₃₂ =>
      subst res
      simp at ih₁ ih₂ ih₃
      specialize ih₁ _ _ .val h₂ h₃₁ rfl rfl
      specialize ih₂ _ _ cat' ih₁.2 h₃₂ rfl rfl
      exact ih₃ _ _ .val ih₂.2 (.loop _ _ cat' h₃₁ h₃₂) rfl rfl
  | loopStop st st' x₁ x₂ y₁ h₄ h₅ ih =>
    cases h₃ with
    | loop _ _ _ h₃₁ h₃₂ =>
      simp at hr
      obtain ⟨ rfl, rfl ⟩ := hr
      specialize ih _ _ .val h₂ h₃₁ rfl
      simp [ih]
  | loopErr => simp at hr
  | loopErrL => simp at hr
  | loopErrR => simp at hr
  | caseOk st st₁ x₁ bs y₁ env x₂ res h₄ h₅ h₆ ih₁ ih₂ =>
    apply Result.popEnv_state at hr
    obtain ⟨ str, rfl, hr ⟩ := hr
    specialize ih₁ _ _ .val h₂ ?_ rfl
    . cases h₃ with
      | caseVal _ _ h₃ => exact h₃
      | caseRef _ _ _ h₃ => exact h₃
    have cat' : ∃ cat', x₂.WF cat' ∧ (∀ v : Value, v.HasCategory cat' -> v.HasCategory cat) := by
      cases h₃ with
      | caseVal _ _ _ h₃ =>
        apply chooseCase_expr_wf_val at h₅
        . use .val
          simp [h₅]
        . assumption
      | caseRef _ _ xs _ _ h₃ =>
        apply chooseCase_expr_wf_ref at h₅
        on_goal 3 => assumption
        obtain ⟨ i, h₅, - ⟩ := h₅
        use .ref xs[i]
        and_intros
        . assumption
        simp
        intro _ x rfl h
        simp
        cases x <;> simp
        simp at h
        use i
        exact h
    obtain ⟨ cat', hc₁, hc₂ ⟩ := cat'
    specialize ih₂ _ _ cat' ?_ hc₁ rfl
    . simp [State.CategoryWF_iff, ih₁.2.mem, ih₁.2.env]
      apply chooseCase_env_category_wf at h₅
      assumption
    and_intros
    . apply hc₂
      simp [ih₂]
    replace ih₂ := ih₂.2
    unfold State.popEnv at hr
    simp [Option.bind] at hr
    split at hr <;> simp at hr
    subst hr
    rename_i env' hr
    unfold Environment.pop at hr
    split at hr <;> simp at hr
    subst hr
    rename_i env' hr
    simp [State.CategoryWF_iff, ih₂.mem]
    replace ih := ih₂.env
    simp [hr] at ih
    simp [ih]
  | caseErr₁ => simp at hr
  | caseErr₂ => simp at hr
  | scope st x₁ env x₂ res h₄ h₅ ih =>
    apply Result.popEnv_state at hr
    obtain ⟨ str, rfl, hr ⟩ := hr
    specialize ih _ _ cat ?_ ?_ rfl
    . simp [State.CategoryWF_iff, h₂.mem, h₂.env]
      apply prepareDefList_env_category_wf at h₄
      . assumption
      cases h₃ with
      | scopeVal => simp; assumption
      | scopeRef => simp; assumption
    . constructor
      . apply prepareDefList_expr_wf at h₄
        . assumption
        cases h₃ with
        | scopeVal => simp; assumption
        | scopeRef => simp; assumption
      cases h₃ with
      | scopeVal => simp [*]
      | scopeRef => simp [*]
    simp [ih]
    unfold State.popEnv at hr
    simp [Option.bind] at hr
    split at hr <;> simp at hr
    subst hr
    rename_i env' hr
    unfold Environment.pop at hr
    split at hr <;> simp at hr
    subst hr
    rename_i env' hr
    simp [State.CategoryWF_iff, ih.2.mem]
    replace ih := ih.2.env
    simp [hr] at ih
    simp [ih]
  | nil st h₂ h₃ xs st' hr =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    assumption
  | cons st₁ st₂ st₃ x xs y ys h₄ h₅ ih₁ ih₂ h₂ h₃ xs' st' hr =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih₁ ih₂
    specialize ih₁ _ _ .val h₂ (h₃ x (by simp)) rfl rfl
    apply ih₂ ih₁.2
    intro e he
    apply h₃ e
    simp [he]
  | err _ _ _ _ _ _ _ _ _ _ _ hr => simp at hr
  | errL _ _ _ _ _ _ _ _ _ _ hr => simp at hr
  | errR _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr => simp at hr

theorem EvalList_category_wf (st st' : State) (es : List Expr)
                             (xs : List RValue)
                             (h₁ : st.CategoryWF)
                             (h₂ : ∀ e ∈ es, e.WF .val)
                             (h₃ : EvalList st es (.ok xs st'))
: st'.CategoryWF := by
  induction es generalizing st st' xs with
  | nil =>
    cases h₃ with
    | nil => assumption
  | cons e es ih =>
    cases h₃ with
    | cons _ st₁ _ _ _ x xs h₃ h₄ =>
      apply Eval_category_wf at h₃
      on_goal 3 => assumption
      on_goal 3 =>
        apply h₂
        simp
      apply ih at h₄
      . assumption
      . simp [h₃]
      intro e he
      apply h₂
      simp [he]
