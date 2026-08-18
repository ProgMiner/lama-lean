import Mathlib

import Lama.Semantics.Eval

namespace Lama.Semantics


open Lama.Ast

def EnvValue.SameShape : EnvValue -> EnvValue -> Prop
| var _, var _ => True
| fn xs₁ b₁, fn xs₂ b₂ => xs₁ = xs₂ ∧ b₁ = b₂
| _, _ => False

@[refl, simp]
theorem EnvValue.SameShape_refl (x : EnvValue) : x.SameShape x := by
  cases x <;> simp [SameShape]

instance : Std.Refl EnvValue.SameShape := ⟨ EnvValue.SameShape_refl ⟩

@[symm]
theorem EnvValue.SameShape_symm (x y : EnvValue)
                                (h : x.SameShape y)
: y.SameShape x := by
  cases x <;> cases y <;> simp [SameShape] at *
  simp [*]

instance : Std.Symm EnvValue.SameShape := ⟨ EnvValue.SameShape_symm ⟩

@[trans]
theorem EnvValue.SameShape_trans (x y z : EnvValue)
                                 (h₁ : x.SameShape y)
                                 (h₂ : y.SameShape z)
: x.SameShape z := by
  cases x <;> cases y <;> cases z <;>
  all_goals simp [SameShape] at *
  simp [*]

instance : IsTrans _ EnvValue.SameShape := ⟨ EnvValue.SameShape_trans ⟩

def EnvValue.SameShape'
: Option EnvValue -> Option EnvValue -> Prop
| .some x, .some y => x.SameShape y
| .none, .none => True
| _, _ => False

@[refl, simp]
theorem EnvValue.SameShape'_refl (x : Option EnvValue)
: EnvValue.SameShape' x x := by
  cases x <;> simp [SameShape']

instance : Std.Refl EnvValue.SameShape' := ⟨ EnvValue.SameShape'_refl ⟩

@[symm]
theorem EnvValue.SameShape'_symm (x y : Option EnvValue)
                                 (h : EnvValue.SameShape' x y)
: EnvValue.SameShape' y x := by
  cases x <;> cases y <;> simp [SameShape'] at *
  symm; assumption

instance : Std.Symm EnvValue.SameShape' := ⟨ EnvValue.SameShape'_symm ⟩

@[trans]
theorem EnvValue.SameShape'_trans (x y z : Option EnvValue)
                                  (h₁ : EnvValue.SameShape' x y)
                                  (h₂ : EnvValue.SameShape' y z)
: EnvValue.SameShape' x z := by
  cases x <;> cases y <;> cases z
  all_goals simp [SameShape'] at *
  trans <;> assumption

instance : IsTrans _ EnvValue.SameShape' := ⟨ EnvValue.SameShape'_trans ⟩

def SimpleEnv.SameShape (xs₁ xs₂ : SimpleEnv) : Prop :=
  ∀ x, EnvValue.SameShape' (xs₁.lookup x) (xs₂.lookup x)

@[refl, simp]
theorem SimpleEnv.SameShape_refl (xs : SimpleEnv)
: xs.SameShape xs := by
  simp [SameShape]

instance : Std.Refl SimpleEnv.SameShape := ⟨ SimpleEnv.SameShape_refl ⟩

@[symm]
theorem SimpleEnv.SameShape_symm (xs ys : SimpleEnv)
                                 (h : xs.SameShape ys)
: ys.SameShape xs := by
  simp [SameShape] at *
  intro x; symm; apply h

instance : Std.Symm SimpleEnv.SameShape := ⟨ SimpleEnv.SameShape_symm ⟩

@[trans]
theorem SimpleEnv.SameShape_trans (xs ys zs : SimpleEnv)
                                  (h₁ : xs.SameShape ys)
                                  (h₂ : ys.SameShape zs)
: xs.SameShape zs := by
  simp [SameShape] at *
  intro x; trans
  . apply h₁
  . apply h₂

instance : IsTrans _ SimpleEnv.SameShape := ⟨ SimpleEnv.SameShape_trans ⟩

def BoxValue.SameShape : BoxValue -> BoxValue -> Prop
| undefined, undefined => True
| str _, str _ => True
| arr _, arr _ => True
| sexp _ _, sexp _ _ => True
| closure env₁ xs₁ b₁, closure env₂ xs₂ b₂ =>
  env₁.SameShape env₂ ∧ xs₁ = xs₂ ∧ b₁ = b₂
| _, _ => False

@[simp]
theorem BoxValue.SameShape_undefined (x : BoxValue)
: x.SameShape undefined <-> x = undefined := by
  cases x <;> simp [SameShape]

@[refl, simp]
theorem BoxValue.SameShape_refl (x : BoxValue) : x.SameShape x := by
  cases x <;> simp [SameShape]

instance : Std.Refl BoxValue.SameShape := ⟨ BoxValue.SameShape_refl ⟩

@[symm]
theorem BoxValue.SameShape_symm (x y : BoxValue)
                                (h : x.SameShape y)
: y.SameShape x := by
  cases x <;> cases y <;> simp [SameShape] at *
  simp [*]; symm; simp [h]

instance : Std.Symm BoxValue.SameShape := ⟨ BoxValue.SameShape_symm ⟩

@[trans]
theorem BoxValue.SameShape_trans (x y z : BoxValue)
                                 (h₁ : x.SameShape y)
                                 (h₂ : y.SameShape z)
: x.SameShape z := by
  cases x <;> cases y <;> cases z
  all_goals simp [SameShape] at *
  obtain ⟨ h₁, rfl, rfl ⟩ := h₁
  obtain ⟨ h₂, rfl, rfl ⟩ := h₂
  simp; trans <;> assumption

instance : IsTrans _ BoxValue.SameShape := ⟨ BoxValue.SameShape_trans ⟩

theorem BoxValue.assign_same_shape (x x' : BoxValue)
                                   (i : ℕ) (y : RValue)
                                   (h : x.assign i y = .ok x')
: x.SameShape x' := by
  fun_cases assign with
  | case1 => simp at h
  | case2 =>
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    subst h
    simp [SameShape]
  | case3 =>
    simp [Functor.map, Except.map] at h
    split at h <;> try simp at h
    subst h
    simp [SameShape]
  | case4 =>
    simp [Functor.map, Except.map] at h
    split at h <;> try simp at h
    subst h
    simp [SameShape]
  | case5 => simp at h

structure Memory.LE (m m' : Memory) : Prop where
  bound : m.bound ≤ m'.bound
  vals : ∀ b, b.cell < m.bound -> (m b).SameShape (m' b)

@[reducible]
instance : LE Memory where
  le := Memory.LE

theorem Memory.LE_iff (m m' : Memory)
: m ≤ m' <-> m.bound ≤ m'.bound ∧ ∀ b, b.cell < m.bound -> (m.mem b).SameShape (m'.mem b) where
  mp := by
    intro ⟨ h₁, h₂ ⟩
    exact ⟨ h₁, h₂ ⟩
  mpr := by
    intro ⟨ h₁, h₂ ⟩
    exact ⟨ h₁, h₂ ⟩

instance : Preorder Memory where
  le_refl := by simp [Memory.LE_iff]
  le_trans m₁ m₂ m₃ h₁ h₂ := by
    simp [Memory.LE_iff] at *
    and_intros
    . grw [h₁.1, h₂.1]
    intro b hb
    have hb' := hb
    grw [h₁.1] at hb'
    replace h₁ := h₁.2 _ hb
    replace h₂ := h₂.2 _ hb'
    trans <;> assumption

theorem Memory.alloc_monotonic (mem : Memory)
: mem ≤ mem.alloc.2 := by
  simp [Memory.LE_iff]

theorem Memory.assign_monotonic (mem : Memory)
                                (box : Box) (value : BoxValue)
                                (h : (mem box).SameShape value)
: mem ≤ mem.assign box value := by
  simp [Memory.LE_iff]
  intro b hb
  split_ifs with hb'
  on_goal 2 => rfl
  subst b
  assumption

theorem Memory.allocWith_monotonic (mem mem' : Memory)
                                   (x : BoxValue) (b : Box)
                                   (h : mem.allocWith x = (b, mem'))
: mem ≤ mem' := by
  simp at h
  obtain ⟨ rfl, rfl ⟩ := h
  simp [Memory.LE_iff]
  intro b h
  split_ifs with h'
  on_goal 2 => simp
  subst b
  simp at h

theorem Environment.assign_memory_monotonic (x : Ident) (y : RValue)
                                            (mem mem' : Memory) (env env' : Environment)
                                            (h : env.assign x y mem = .ok (env', mem'))
: mem ≤ mem' := by
  fun_induction assign generalizing mem' env' with
  | case1 => simp at h
  | case2 b xs params body h₁ x' h₂ xs' mem' =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    subst xs' mem'
    simp at h₁
    simp [Memory.LE_iff]
    intro b' h
    split_ifs with h
    on_goal 2 => simp
    subst b'
    simp [h₁, BoxValue.SameShape, SimpleEnv.SameShape]
    intro x'
    by_cases hx : x' = x
    on_goal 2 => simp [Finmap.lookup_insert_of_ne, hx]
    subst x'
    simp [h₂, EnvValue.SameShape', EnvValue.SameShape]
  | case3 => simp at h
  | case4 => simp at h
  | case5 =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
  | case6 => simp at h
  | case7 xt env h ih =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    rename_i h'
    specialize ih _ _ h'
    assumption

@[simp]
def Environment.SameShape
: Environment -> Environment -> Prop
| empty, empty => True
| closure b₁, closure b₂ => b₁ = b₂
| scope xs₁ env₁, scope xs₂ env₂ =>
  xs₁.SameShape xs₂ ∧ env₁.SameShape env₂
| _, _ => False

@[refl, simp]
theorem Environment.SameShape_refl (x : Environment) : x.SameShape x := by
  induction x <;> simp [*]

instance : Std.Refl Environment.SameShape := ⟨ Environment.SameShape_refl ⟩

@[symm]
theorem Environment.SameShape_symm (x y : Environment)
                                   (h : x.SameShape y)
: y.SameShape x := by
  fun_induction SameShape x y with
  | case1 => simp
  | case2 => simp [h]
  | case4 => simp at h
  | case3 xs₁ env₁ xs₂ env₂ ih =>
    simp
    and_intros
    on_goal 2 =>
      apply ih
      simp [h]
    intro x
    symm
    apply h.1

instance : Std.Symm Environment.SameShape := ⟨ Environment.SameShape_symm ⟩

@[trans]
theorem Environment.SameShape_trans (x y z : Environment)
                                    (h₁ : x.SameShape y)
                                    (h₂ : y.SameShape z)
: x.SameShape z := by
  fun_induction SameShape x y generalizing z with
  | case1 => assumption
  | case2 => simp [*]
  | case4 => simp at h₁
  | case3 xs₁ env₁ xs₂ env₂ ih =>
    cases z <;> simp at *
    case scope xs₃ env₃ =>
      specialize ih _ h₁.2 h₂.2
      simp [ih]
      intro x
      replace h₁ := h₁.1 x
      replace h₂ := h₂.1 x
      trans <;> assumption

instance : IsTrans _ Environment.SameShape := ⟨ Environment.SameShape_trans ⟩

theorem Environment.assign_same_shape (x : Ident) (y : RValue)
                                      (mem mem' : Memory) (env env' : Environment)
                                      (h : env.assign x y mem = .ok (env', mem'))
: env.SameShape env' := by
  fun_induction assign generalizing env' mem' with
  | case1 => simp at h
  | case2 =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
  | case3 => simp at h
  | case4 => simp at h
  | case5 xs env y' h =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
    intro x'
    by_cases hx : x' = x
    on_goal 2 => simp [Finmap.lookup_insert_of_ne, hx]
    subst x'
    simp [h, EnvValue.SameShape', EnvValue.SameShape]
  | case6 => simp at h
  | case7 xs env h ih =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    rename_i h'
    specialize ih _ _ h'
    simp [ih]

structure State.LE (st st' : State) : Prop where
  mem : st.mem ≤ st'.mem
  env : st.env.SameShape st'.env

@[reducible]
instance : LE State where
  le := State.LE

theorem State.LE_iff (st st' : State)
: st ≤ st' <-> st.mem ≤ st'.mem ∧ st.env.SameShape st'.env where
  mp := by
    intro ⟨ h₁, h₂ ⟩
    exact ⟨ h₁, h₂ ⟩
  mpr := by
    intro ⟨ h₁, h₂ ⟩
    exact ⟨ h₁, h₂ ⟩

instance : Preorder State where
  le_refl st := by simp [State.LE_iff]
  le_trans st₁ st₂ st₃ h₁ h₂ := by
    simp [State.LE_iff] at *
    and_intros
    . trans; exact h₁.1; exact h₂.1
    . trans; exact h₁.2; exact h₂.2

theorem State.allocWith_monotonic (st st' : State)
                                  (x : BoxValue) (b : Box)
                                  (h : st.allocWith x = (b, st'))
: st ≤ st' := by
  simp at h
  obtain ⟨ rfl, rfl ⟩ := h
  simp [State.LE_iff]
  apply Memory.allocWith_monotonic
  rfl

theorem State.popEnv_state (r : Result Value) (x : Value) (st : State)
                           (h : r.popEnv = Result.ok x st)
: ∃ st' : State, r = .ok x st' ∧ st'.popEnv = .some st := by
  unfold Result.popEnv at h
  cases r with
  | err => simp at h
  | ok x' st' =>
    split at h <;> rename_i h' <;> simp at h'
    obtain ⟨ rfl, rfl ⟩ := h'
    extract_lets at h
    rename_i ok; clear_value ok
    split_ifs at h
    subst ok
    split at h <;> simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    use st'

theorem evalVar_state_monotonic (st st' : State)
                                (x : Ident) (y : RValue)
                                (h : evalVar st x = .ok (y, st'))
: st ≤ st' := by
  unfold evalVar at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  generalize Environment.lookup x st.mem st.env = x' at h
  cases x' <;> simp at h
  rename_i x'
  cases x' <;> simp at h
  . obtain ⟨ rfl, rfl ⟩ := h
    simp
  rename_i env params body
  generalize Environment.close st.mem env = env' at h
  cases env' <;> simp at h
  obtain ⟨ rfl, rfl ⟩ := h
  apply State.allocWith_monotonic
  rfl

theorem prepareCall_state (mem : Memory) (x : Value) (xs : List RValue)
                          (st : State) (body : Expr)
                          (h : prepareCall mem x xs = .ok (st, body))
: mem = st.mem := by
  unfold prepareCall at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  obtain ⟨ rfl, rfl ⟩ := h
  simp

theorem evalAssign_state_monotonic (st st' : State)
                                   (x y : Value) (z : RValue)
                                   (h : evalAssign st x y = .ok (st', z))
: st ≤ st' := by
  unfold evalAssign at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  obtain ⟨ rfl, rfl ⟩ := h
  rename_i h₁ _ _ h₂
  cases y <;> simp at h₁
  subst h₁
  rename_i x1 x2 st' y
  clear x1 x2
  unfold evalAssignR at h₂
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₂
  split at h₂ <;> try simp at h₂
  split at h₂ <;> try simp at h₂
  split at h₂ <;> try simp at h₂
  . subst st'
    simp [State.LE_iff]
    and_intros
    . apply Environment.assign_memory_monotonic
      assumption
    . apply Environment.assign_same_shape
      assumption
  split at h₂ <;> try simp at h₂
  subst st'
  simp [State.LE_iff, Memory.LE_iff]
  intro b hb
  rename_i h
  apply BoxValue.assign_same_shape at h
  split_ifs <;> try simp
  subst b
  assumption

theorem Eval_state_monotonic (st st' : State) (e : Expr) (x : Value)
                             (h : Eval st e (.ok x st'))
: st ≤ st' := by
  generalize hr : Result.ok x st' = r at h
  symm at hr
  induction h
  using Eval.rec (motive_2 := fun st es r _ => ∀ x st', .ok x st' = r -> st ≤ st')
  generalizing st' x with
  | skip =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    rfl
  | varOk st st' x y h =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply evalVar_state_monotonic at h
    assumption
  | varErr => simp at hr
  | refOk =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp
  | refErr => simp at hr
  | int =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    rfl
  | str st st' s box h =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply State.allocWith_monotonic at h
    assumption
  | arrOk st₁ st₂ st₃ xs ys box h₁ h₂ ih =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih
    apply State.allocWith_monotonic at h₂
    grw [ih, h₂]
  | arrErr => simp at hr
  | sexpOk st₁ st₂ st₃ t xs ys box h₁ h₂ ih =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih
    apply State.allocWith_monotonic at h₂
    grw [ih, h₂]
  | sexpErr => simp at hr
  | lambdaOk st st' xs x box env h₁ h₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply State.allocWith_monotonic at h₂
    assumption
  | lambdaErr => simp at hr
  | binopOk st₁ st₂ st₃ op x₁ x₂ y₁ y₂ z h₁ h₂ h₃ ih₁ ih₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih₁ ih₂
    grw [ih₁, ih₂]
  | binopErr => simp at hr
  | binopErrL => simp at hr
  | binopErrR => simp at hr
  | elemOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₁ h₂ h₃ ih₁ ih₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih₁ ih₂
    grw [ih₁, ih₂]
  | elemErr => simp at hr
  | elemErrL => simp at hr
  | elemErrR => simp at hr
  | elemRefOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₁ h₂ h₃ ih₁ ih₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih₁ ih₂
    grw [ih₁, ih₂]
  | elemRefErr => simp at hr
  | elemRefErrL => simp at hr
  | elemRefErrR => simp at hr
  | callOk st₁ st₂ st₃ st₄ st₅ x xs y ys z z' h₁ h₂ h₃ h₄ ih₁ ih₂ ih₃ =>
    simp at ih₁ ih₂ ih₃
    grw [ih₁, ih₂]
    unfold commitCall at hr
    cases z' <;> simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp [State.LE_iff] at ih₃ ⊢
    apply prepareCall_state at h₃
    grw [<- ih₃.1, h₃]
  | callErr₁ => simp at hr
  | callErr₂ => simp at hr
  | callErr₃ => simp at hr
  | callErr₄ => simp at hr
  | assignOk st₁ st₂ st₃ st₄ x₁ x₂ y₁ y₂ z h₁ h₂ h₃ ih₁ ih₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih₁ ih₂
    apply evalAssign_state_monotonic at h₃
    grw [ih₁, ih₂, h₃]
  | assignErr => simp at hr
  | assignErrL => simp at hr
  | assignErrR => simp at hr
  | seqOk st₁ st₂ x₁ x₂ y₁ res h₁ h₂ ih₁ ih₂ =>
    subst res
    simp at ih₁ ih₂
    grw [ih₁, ih₂]
  | seqErr => simp at hr
  | iteThen st st' x₁ x₂ x₃ y₁ res h₁ h₂ h₃ ih₁ ih₂ =>
    subst res
    simp at ih₁ ih₂
    grw [ih₁, ih₂]
  | iteElse st st' x₁ x₂ x₃ y₁ res h₁ h₂ h₃ ih₁ ih₂ =>
    subst res
    simp at ih₁ ih₂
    grw [ih₁, ih₂]
  | iteErr₁ => simp at hr
  | iteErr₂ => simp at hr
  | loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res h₁ h₂ h₃ h₄ ih₁ ih₂ ih₃ =>
    subst res
    simp at ih₁ ih₂ ih₃
    grw [ih₁, ih₂, ih₃]
  | loopStop st st' x₁ x₂ y₁ h₁ h₂ ih =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih
    assumption
  | loopErr => simp at hr
  | loopErrL => simp at hr
  | loopErrR => simp at hr
  | caseOk st st' x₁ bs y₁ env x₂ res h₁ h₂ h₃ ih₁ ih₂ =>
    apply State.popEnv_state at hr
    obtain ⟨ str, rfl, hr ⟩ := hr
    simp at ih₁ ih₂
    grw [ih₁]
    unfold State.popEnv at hr
    simp [Option.bind] at hr
    split at hr <;> simp at hr
    subst st'
    rename_i envr h
    unfold State.pushEnv at ih₂
    simp [State.LE_iff] at ih₂ ⊢
    simp [ih₂]
    unfold Environment.pop at h
    split at h <;> simp at h
    subst envr
    rename_i h
    rw [h] at ih₂
    simp at ih₂
    simp [ih₂]
  | caseErr₁ => simp at hr
  | caseErr₂ => simp at hr
  | scope st x₁ env x₂ res h₁ h₂ ih =>
    apply State.popEnv_state at hr
    obtain ⟨ str, rfl, hr ⟩ := hr
    simp at ih
    unfold State.popEnv at hr
    simp [Option.bind] at hr
    split at hr <;> simp at hr
    subst st'
    rename_i envr h
    unfold State.pushEnv at ih
    simp [State.LE_iff] at ih ⊢
    simp [ih]
    unfold Environment.pop at h
    split at h <;> simp at h
    subst envr
    rename_i h
    rw [h] at ih
    simp at ih
    simp [ih]
  | nil st x st' hr =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    rfl
  | cons st₁ st₂ st₃ x xs y ys h₁ h₂ ih₁ ih₂ x st' hr =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at ih₁ ih₂
    grw [ih₁, ih₂]
  | err _ _ _ _ _ _ _ _ _ hr => simp at hr
  | errL _ _ _ _ _ _ _ _ hr => simp at hr
  | errR _ _ _ _ _ _ _ _ _ _ _ _ hr => simp at hr

theorem EvalList_state_monotonic (st st' : State)
                                 (es : List Expr) (xs : List RValue)
                                 (h : EvalList st es (.ok xs st'))
: st ≤ st' := by
  induction es generalizing st st' xs with
  | nil =>
    cases h with
    | nil => simp
  | cons e es ih =>
    cases h with
    | cons _ st₂ _ _ _ x xs h₁ h₂ =>
      apply Eval_state_monotonic at h₁
      apply ih at h₂
      grw [h₁, h₂]
