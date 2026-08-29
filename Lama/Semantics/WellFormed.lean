import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.SuccPred

import Lama.Semantics.Monotonic


namespace Lama.Semantics

open Lama.Ast

abbrev Box.WF (mem : Memory) (box : Box) : Prop :=
  box.cell < mem.bound

theorem Box.WF_transport (mem mem' : Memory) (b : Box)
                         (h₁ : mem ≤ mem') (h₂ : b.WF mem)
: b.WF mem' := by
  rw [Memory.LE_iff] at h₁
  unfold WF at *
  exact h₂.trans_le h₁.1

def RValue.WF (mem : Memory) : RValue -> Prop
| int _ => True
| box b => b.WF mem

@[simp]
theorem RValue.WF_int (mem : Memory) (x : ℤ)
: WF mem (int x) := True.intro

@[simp]
theorem RValue.WF_box (mem : Memory) (b : Box)
: WF mem (box b) <-> b.WF mem := by rfl

theorem RValue.WF_transport (mem mem' : Memory) (x : RValue)
                            (h₁ : mem ≤ mem') (h₂ : x.WF mem)
: x.WF mem' := by
  cases x with
  | int => trivial
  | box b => exact b.WF_transport _ _ h₁ h₂

def EnvValue.WF (mem : Memory) : EnvValue -> Prop
| var x => x.WF mem
| fn _ _ => True

@[simp]
theorem EnvValue.WF_var (mem : Memory) (x : RValue)
: WF mem (var x) <-> x.WF mem := by rfl

@[simp]
theorem EnvValue.WF_fn (mem : Memory) (xs : List Ident) (body : Expr)
: WF mem (fn xs body) := True.intro

def SimpleEnv.WF (mem : Memory) (env : SimpleEnv) :=
  ∀ x y, env.lookup x = .some y -> y.WF mem

theorem SimpleEnv.WF_transport (mem mem' : Memory) (env : SimpleEnv)
                               (h₁ : mem ≤ mem') (h₂ : env.WF mem)
: env.WF mem' := by
  intro x y hy
  cases y with
  | var y => exact y.WF_transport _ _ h₁ (h₂ _ _ hy)
  | fn _ _ => trivial

theorem SimpleEnv.insert_wf (mem : Memory) (env : SimpleEnv)
                            (x : Ident) (y : EnvValue)
                            (h₁ : env.WF mem) (h₂ : y.WF mem)
: WF mem (Finmap.insert x y env) := by
  intro x' y' hy'
  by_cases hx' : x' = x
  . subst x'
    simp at hy'
    subst y'
    assumption
  rw [Finmap.lookup_insert_of_ne _ hx'] at hy'
  apply h₁ _ _ hy'

theorem SimpleEnv.union_wf (mem : Memory) (env₁ env₂ : SimpleEnv)
                           (h₁ : env₁.WF mem) (h₂ : env₂.WF mem)
: WF mem (env₁ ∪ env₂) := by
  intro x y hy
  simp at hy
  obtain hy | ⟨ _, hy ⟩ := hy
  . apply h₁ at hy
    assumption
  . apply h₂ at hy
    assumption

@[reducible, simp]
def ClosedEnv.WF (mem : Memory)
: ClosedEnv → Prop
| .empty => True
| .scope xs env => xs.WF mem ∧ ClosedEnv.WF mem env

@[simp]
theorem ClosedEnv.empty_wf (mem : Memory)
: WF mem ∅ := True.intro

theorem ClosedEnv.WF_transport (mem mem' : Memory)
                               (env : ClosedEnv)
                               (h₁ : mem ≤ mem')
                               (h₂ : env.WF mem)
: env.WF mem' := by
  fun_induction env.WF mem with
  | case1 => simp
  | case2 xs env ih =>
    simp [ih, h₂]
    exact SimpleEnv.WF_transport _ _ _ h₁ h₂.1

def EnvLookup.WF (mem : Memory) : EnvLookup -> Prop
| var x => x.WF mem
| fn env _ _ => env.WF mem

@[simp]
theorem EnvLookup.WF_var (mem : Memory) (x : RValue)
: WF mem (var x) <-> x.WF mem := by rfl

@[simp]
theorem EnvLookup.WF_fn (mem : Memory) (env : ClosedEnv)
                        (params : List Ident) (body : Expr)
: WF mem (fn env params body) <-> env.WF mem := by rfl

theorem EnvValue.toLookup_wf (mem : Memory) (env : ClosedEnv) (x : EnvValue)
                             (h₁ : env.WF mem) (h₂ : x.WF mem)
: (x.toLookup env).WF mem := by
  cases x with
  | var => exact h₂
  | fn => exact h₁

theorem ClosedEnv.lookup_wf (env : ClosedEnv) (mem : Memory)
                            (x : Ident) (res : EnvLookup)
                            (h₁ : env.lookup x = .some res)
                            (h₂ : env.WF mem)
: res.WF mem := by
  fun_induction lookup with
  | case1 => simp at h₁
  | case2 xs env y h =>
    simp at h₁
    subst h₁
    apply EnvValue.toLookup_wf
    . assumption
    apply h₂.1
    assumption
  | case3 xs env h ih =>
    apply ih
    . assumption
    . exact h₂.2

theorem ClosedEnv.assign_wf (x : Ident) (y : RValue)
                            (env env' : ClosedEnv)
                            (mem : Memory)
                            (h₁ : env.WF mem) (h₂ : y.WF mem)
                            (h₃ : env.assign x y = .some env')
: env'.WF mem := by
  fun_induction assign generalizing env' with
  | case1 => simp at h₃
  | case2 xs env y' h =>
    simp at h₃
    subst h₃
    simp at h₁
    simp [h₁]
    apply SimpleEnv.insert_wf
    . simp [h₁]
    . simp [h₂]
  | case3 => simp at h₃
  | case4 xs env h ih =>
    simp [Option.bind] at h₃
    split at h₃ <;> simp at h₃
    subst env'
    rename_i env' h
    simp at h₁
    simp [h₁]
    apply ih
    . simp [h₁]
    . assumption

def BoxValue.WF (mem : Memory) : BoxValue -> Prop
| undefined => True
| str _ => True
| arr xs => ∀ x ∈ xs, x.WF mem
| sexp _ xs => ∀ x ∈ xs, x.WF mem
| closure env _ _ => env.WF mem

@[simp]
theorem BoxValue.WF_undefined (mem : Memory)
: WF mem undefined := True.intro

@[simp]
theorem BoxValue.WF_str (mem : Memory) (xs : ByteArray)
: WF mem (str xs) := True.intro

@[simp]
theorem BoxValue.WF_arr (mem : Memory) (xs : List RValue)
: WF mem (arr xs) <-> ∀ x ∈ xs, x.WF mem := by rfl

@[simp]
theorem BoxValue.WF_sexp (mem : Memory) (t : Tag) (xs : List RValue)
: WF mem (sexp t xs) <-> ∀ x ∈ xs, x.WF mem := by rfl

@[simp]
theorem BoxValue.WF_closure (mem : Memory) (env : ClosedEnv)
                            (xs : List Ident) (body : Expr)
: WF mem (closure env xs body) <-> env.WF mem := by rfl

theorem BoxValue.WF_transport (mem mem' : Memory) (x : BoxValue)
                              (h₁ : mem ≤ mem') (h₂ : x.WF mem)
: x.WF mem' := by
  cases x with
  | undefined => trivial
  | str _ => trivial
  | arr xs =>
    intro y hy
    exact y.WF_transport _ _ h₁ (h₂ _ hy)
  | sexp _ xs =>
    intro y hy
    exact y.WF_transport _ _ h₁ (h₂ _ hy)
  | closure env _ _ =>
    exact env.WF_transport _ _ h₁ h₂

theorem BoxValue.assign_wf (mem : Memory) (x z : BoxValue)
                           (i : ℕ) (y : RValue)
                           (h₁ : x.WF mem) (h₂ : y.WF mem)
                           (h₃ : x.assign i y = .ok z)
: z.WF mem := by
  cases x <;> simp only [WF, assign, reduceCtorEq] at h₁ h₃
  . simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₃
    split at h₃ <;> try simp at h₃
    split at h₃ <;> try simp at h₃
    subst z
    simp
  case arr xs =>
    simp [Functor.map, Except.map] at h₃
    split at h₃ <;> simp at h₃
    rename_i xs' hxs'
    simp at hxs'
    obtain ⟨ hi, rfl ⟩ := hxs'
    subst z
    intro x hx
    apply List.mem_or_eq_of_mem_set at hx
    obtain hx | rfl := hx
    . apply h₁
      assumption
    . assumption
  case sexp xs =>
    simp [Functor.map, Except.map] at h₃
    split at h₃ <;> simp at h₃
    rename_i xs' hxs'
    simp at hxs'
    obtain ⟨ hi, rfl ⟩ := hxs'
    subst z
    intro x hx
    apply List.mem_or_eq_of_mem_set at hx
    obtain hx | rfl := hx
    . apply h₁
      assumption
    . assumption

structure Memory.WF (m : Memory) : Prop where
  bound : ∀ b, m b = .undefined <-> ¬ b.WF m
  mem : ∀ b, (m b).WF m

theorem Memory.WF_iff (m : Memory)
: m.WF <-> (∀ b, m b = .undefined <-> ¬ b.WF m) ∧ (∀ b, (m b).WF m) where
  mp h := by
    obtain ⟨ h₁, h₂ ⟩ := h
    exact ⟨ h₁, h₂ ⟩
  mpr h := by
    obtain ⟨ h₁, h₂ ⟩ := h
    exact ⟨ h₁, h₂ ⟩

@[simp]
theorem Memory.empty_wf : WF ∅ := by
  simp [Memory.WF_iff, EmptyCollection.emptyCollection, empty]

theorem Memory.assign_wf (box : Box) (value : BoxValue) (mem : Memory)
                         (h₁ : mem.WF) (h₂ : value.WF mem)
                         (h₃ : (mem box).SameShape value)
: (mem.assign box value).WF := by
  simp [WF_iff]
  and_intros <;> intro b
  . split_ifs
    . subst b
      have := h₁.bound box
      simp at this
      rw [<- this]
      repeat rw [<- BoxValue.SameShape_undefined]
      constructor <;> intro h <;> trans <;> try assumption
      symm; assumption
    . simp [h₁.bound]
  . apply BoxValue.WF_transport
    . apply assign_monotonic
      assumption
    split_ifs with hb
    . subst b
      assumption
    apply h₁.mem

theorem Memory.allocWith_wf (mem mem' : Memory) (x : BoxValue) (b : Box)
                            (h₁ : mem.WF) (h₂ : x.WF mem) (h₃ : x ≠ .undefined)
                            (h₄ : mem.allocWith x = (b, mem'))
: mem'.WF ∧ b.WF mem' := by
  obtain ⟨ rfl, rfl ⟩ := h₄
  simp [WF_iff]
  and_intros <;> intro b
  . split_ifs with hb
    . subst b
      simp [h₃]
    obtain ⟨ b ⟩ := b
    simp at hb ⊢
    simp [h₁.bound]
    lia
  . apply BoxValue.WF_transport mem
    . apply Memory.allocWith_monotonic
      rfl
    split_ifs
    . subst b
      assumption
    . apply h₁.mem

theorem Environment.assign_memory_wf (x : Ident) (y : RValue)
                                     (env env' : Environment)
                                     (mem mem' : Memory)
                                     (h₁ : mem.WF) (h₂ : y.WF mem)
                                     (h₃ : env.assign x y mem = .ok (env', mem'))
: mem'.WF := by
  fun_induction assign generalizing env' mem' with
  | case1 => simp at h₃
  | case2 box env params body h =>
    simp [Functor.map, Except.map] at h₃
    split at h₃ <;> simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    rename_i env' h'
    simp at h'
    apply Memory.assign_wf
    . assumption
    . simp
      apply ClosedEnv.assign_wf at h' <;> try assumption
      have := h₁.mem box
      simp [h] at this
      assumption
    . apply ClosedEnv.assign_same_shape at h'
      symm
      simp [h, h']
  | case3 => simp at h₃
  | case4 =>
    simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    assumption
  | case5 => simp at h₃
  | case6 xs env h ih =>
    simp [Functor.map, Except.map] at h₃
    split at h₃ <;> simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    rename_i h'
    specialize ih _ _ h'
    assumption

@[reducible, simp]
def Environment.WF (mem : Memory)
: Environment → Prop
| .empty => True
| .closure box =>
  ∃ env params body, mem box = .closure env params body
| .scope xs env => xs.WF mem ∧ Environment.WF mem env

@[simp]
theorem Environment.empty_wf (mem : Memory)
: WF mem ∅ := True.intro

theorem Environment.WF_transport (mem mem' : Memory)
                                 (env : Environment)
                                 (h₁ : mem ≤ mem')
                                 (h₂ : mem.WF)
                                 (h₃ : env.WF mem)
: env.WF mem' := by
  fun_induction env.WF mem with
  | case1 => simp
  | case3 xs env ih =>
    simp [ih, h₃]
    exact SimpleEnv.WF_transport _ _ _ h₁ h₃.1
  | case2 box =>
    simp
    rw [Memory.LE_iff] at h₁
    obtain ⟨ env, params, body, h₃ ⟩ := h₃
    replace h₁ := h₁.2 box
    have := h₂.bound box
    simp [h₃] at this
    simp [this, h₃] at h₁
    obtain ⟨ env', h₁, - ⟩ := h₁
    simp [h₁]

theorem Environment.close_wf (mem : Memory) (env : Environment)
                             (env' : ClosedEnv)
                             (h₁ : mem.WF) (h₂ : env.WF mem)
                             (h₃ : env.close mem = .some env')
: env'.WF mem := by
  fun_induction close generalizing env' with
  | case1 =>
    simp at h₃
    subst env'
    simp
  | case2 b xs params body h₃ =>
    simp at h₃
    subst env'
    have := h₁.mem b
    rw [h₃] at this
    exact this
  | case3 => simp at h₃
  | case4 xs env ih =>
    simp [Option.bind] at h₃
    split at h₃ <;> simp at h₃
    subst h₃
    rename_i res h
    simp at h₂
    specialize ih _ h₂.2 h
    simp [h₂, ih]

theorem Environment.close_transport (mem mem' : Memory)
                                    (env : Environment)
                                    (env₁ : ClosedEnv)
                                    (h₁ : mem ≤ mem') (h₂ : mem.WF)
                                    (h₃ : env.close mem = .some env₁)
: ∃ env₂, env.close mem' = .some env₂ ∧ env₁.SameShape env₂ := by
  fun_induction env.close mem generalizing env₁ with
  | case1 =>
    simp at h₃
    subst h₃
    simp
  | case2 box env params body h =>
    simp at h₃
    subst h₃
    have := h₂.bound box
    simp [h] at this
    replace := h₁.vals box this
    simp [h] at this
    obtain ⟨ env', h₄, h₅ ⟩ := this
    simp [h₄, h₅]
  | case3 => simp at h₃
  | case4 xs env ih =>
    simp [Option.bind] at h₃
    split at h₃ <;> simp at h₃
    subst h₃
    rename_i env₁ h
    simp [h] at ih
    obtain ⟨ env₂, ih₁, ih₂ ⟩ := ih
    simp [ih₁, ih₂]

theorem Environment.lookup_transport (mem mem' : Memory) (x : Ident)
                                     (env : Environment) (y : EnvLookup)
                                     (h₁ : mem ≤ mem') (h₂ : mem.WF)
                                     (h₃ : env x mem = .ok y)
: ∃ y', env x mem' = .ok y' ∧ y.SameShape y' := by
  simp at h₃ ⊢
  fun_induction env.lookup x mem with
  | case1 => simp at h₃
  | case2 box env params body h =>
    simp at h₃
    have := h₂.bound box
    simp [h] at this
    replace := h₁.vals box this
    simp [h] at this
    obtain ⟨ env', h₄, h₅ ⟩ := this
    simp [h₄]
    have := ClosedEnv.lookup_same_shape x _ _ h₅
    simp [h₃] at this
    assumption
  | case3 => simp at h₃
  | case4 xs env y h =>
    simp [Functor.map, Except.map] at h₃
    split at h₃ <;> simp at h₃
    subst h₃
    rename_i res h'
    simp [Option.bind] at h'
    split at h' <;> simp at h'
    subst h'
    rename_i res h'
    apply Environment.close_transport _ mem' at h'
    on_goal 2 => assumption
    on_goal 2 => assumption
    obtain ⟨ res', h₃, h₄ ⟩ := h'
    simp [h, h₃]
    apply EnvValue.toLookup_same_shape <;> simp [h₄]
  | case5 xs env h ih =>
    simp [h₃] at ih
    simp [h, ih]

theorem Environment.lookup_wf (env : Environment) (mem : Memory)
                              (x : Ident) (res : EnvLookup)
                              (h₁ : env.lookup x mem = .ok res)
                              (h₂ : mem.WF) (h₃ : env.WF mem)
: res.WF mem := by
  fun_induction lookup with
  | case1 => simp at h₁
  | case2 box xs params body h =>
    simp at h₁
    apply ClosedEnv.lookup_wf at h₁
    apply h₁
    have := h₂.mem box
    simp [h] at this
    assumption
  | case3 => simp at h₁
  | case4 xs env y h' =>
    simp [Functor.map, Except.map] at h₁
    split at h₁ <;> simp at h₁
    subst h₁
    rename_i xs' h
    simp [Option.bind] at h
    split at h <;> simp at h
    subst h
    rename_i env' h
    simp at h₃
    apply EnvValue.toLookup_wf
    . simp [h₃]
      apply close_wf at h
      . assumption
      . assumption
      . exact h₃.2
    . apply h₃.1
      assumption
  | case5 xs env h' ih => exact ih h₁ h₃.2

theorem Environment.assign_wf (x : Ident) (y : RValue)
                              (mem mem' : Memory) (env env' : Environment)
                              (h₁ : env.WF mem) (h₂ : y.WF mem)
                              (h₃ : env.assign x y mem = .ok (env', mem'))
: env'.WF mem := by
  fun_induction assign generalizing env' mem' with
  | case1 => simp at h₃
  | case2 box env params body h =>
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₃
    split at h₃ <;> simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    simp [h]
  | case3 => simp at h₃
  | case4 =>
    simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    simp at h₁ ⊢
    simp [h₁]
    apply SimpleEnv.insert_wf
    . simp [h₁]
    . simp [h₂]
  | case5 => simp at h₃
  | case6 xs env h ih =>
    simp [Functor.map, Except.map] at h₃
    split at h₃ <;> simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    rename_i res h'
    obtain ⟨ env', mem' ⟩ := res
    specialize ih _ _ h₁.2 h'
    simp [ih]
    exact h₁.1

structure State.WF (st : State) : Prop where
  env : st.env.WF st.mem
  mem : st.mem.WF

theorem State.WF_iff (st : State)
: st.WF <-> st.env.WF st.mem ∧ st.mem.WF where
  mp h := by
    obtain ⟨ h₁, h₂ ⟩ := h
    exact ⟨ h₁, h₂ ⟩
  mpr h := by
    obtain ⟨ h₁, h₂ ⟩ := h
    exact ⟨ h₁, h₂ ⟩

@[simp]
theorem State.empty_wf
: WF ∅ := by
  unfold EmptyCollection.emptyCollection
  simp [State.WF_iff]

theorem State.allocWith_wf (st st' : State)
                           (x : BoxValue) (b : Box)
                           (h₁ : st.WF) (h₂ : x.WF st.mem)
                           (h₃ : x ≠ .undefined)
                           (h₄ : st.allocWith x = (b, st'))
: b.WF st'.mem ∧ st'.WF := by
  unfold allocWith at h₄
  split at h₄
  obtain ⟨ rfl, rfl ⟩ := h₄
  rename_i mem' h
  have := Memory.allocWith_wf (h₁ := h₁.mem) (h₂ := h₂) (h₃ := h₃) (h₄ := h)
  simp [WF_iff, this]
  apply Environment.WF_transport st.mem
  . apply Memory.allocWith_monotonic
    assumption
  . apply h₁.mem
  . apply h₁.env

def LValue.WF (st : State) : LValue -> Prop
| var x => ∃ y, st.env x st.mem = .ok (.var y)
| elem b _ => b.WF st.mem

@[simp]
theorem LValue.WF_var (st : State) (x : Ident)
: WF st (var x) <-> ∃ y, st.env x st.mem = .ok (.var y) := by rfl

@[simp]
theorem LValue.WF_elem (st : State) (b : Box) (i : ℕ)
: WF st (elem b i) <-> b.WF st.mem := by rfl

theorem LValue.WF_transport (st st' : State) (x : LValue)
                            (h₁ : st.WF) (h₂ : st ≤ st')
                            (h₃ : x.WF st)
: x.WF st' := by
  cases x with
  | var x =>
    simp at *
    obtain ⟨ y₁, h₃ ⟩ := h₃
    have := Environment.lookup_same_shape x st.mem _ _ h₂.env
    simp [h₃] at this
    obtain ⟨ y₂, h₄ ⟩ := this
    apply Environment.lookup_transport _ st'.mem at h₄
    on_goal 2 => exact h₂.mem
    on_goal 2 => exact h₁.mem
    simp at h₄
    assumption
  | elem b i =>
    simp at h₃ ⊢
    grw [<- h₂.mem.bound]
    assumption

def Value.WF (st : State) : Value -> Prop
| rvalue x => x.WF st.mem
| lvalue x => x.WF st

@[simp]
theorem Value.WF_rvalue (st : State) (x : RValue)
: WF st (rvalue x) <-> x.WF st.mem := by rfl

@[simp]
theorem Value.WF_lvalue (st : State) (x : LValue)
: WF st (lvalue x) <-> x.WF st := by rfl

theorem Value.WF_transport (st st' : State) (x : Value)
                           (h₁ : st.WF) (h₂ : st ≤ st') (h₃ : x.WF st)
: x.WF st' := by
  cases x with
  | rvalue x =>
    apply RValue.WF_transport
    . exact h₂.mem
    . exact h₃
  | lvalue x =>
    apply LValue.WF_transport
    . exact h₁
    . exact h₂
    . exact h₃

def Result.WF {V : Type} (P : V -> State -> Prop)
: Result V -> Prop
| ok x st => P x st ∧ st.WF
| err _ => True

@[simp]
theorem Result.WF_ok {V : Type} {P : V -> State -> Prop}
                     (x : V) (st : State)
: WF P (ok x st) <-> P x st ∧ st.WF := by rfl

@[simp]
theorem Result.WF_err {V : Type} {P : V -> State -> Prop}
                      (e : Error)
: WF P (err e) := True.intro

theorem Result.popEnv_wf (r : Result Value)
                         (h : r.WF (fun x st => x.WF st))
: r.popEnv.WF (fun x st => x.WF st) := by
  cases r with
  | err => simp
  | ok x st' =>
    simp [popEnv]
    split
    case h_2 => simp
    rename_i xs env x h₁
    split_ifs with h₂
    on_goal 2 => simp
    split
    . simp
    rename_i st'' h₃
    simp at h h₂ h₃
    obtain ⟨ env', h₃, rfl ⟩ := h₃
    rw [State.WF_iff] at h
    rw [h₁] at h h₃
    simp at h h₃
    subst env'
    simp [Finmap.lookup_eq_none.mpr h₂] at h
    simp [State.WF_iff, h]

theorem evalVar_wf (st st' : State) (x : Ident) (y : RValue)
                   (h₁ : st.WF) (h₂ : evalVar st x = .ok (y, st'))
: y.WF st'.mem ∧ st'.WF := by
  unfold evalVar at h₂
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₂
  split at h₂ <;> try simp at h₂
  rename_i h₃
  apply Environment.lookup_wf at h₃
  specialize h₃ h₁.mem h₁.env
  split at h₂ <;> try simp at h₂
  . obtain ⟨ rfl, rfl ⟩ := h₂
    simp at h₃
    simp [h₃, h₁]
  obtain ⟨ rfl, rfl ⟩ := h₂
  rename_i env params body
  simp
  refine (State.allocWith_wf _ _ _ _ ?_ ?_ ?_ rfl).2
  on_goal 3 => simp
  . apply h₁
  simp at h₃
  simp [h₃]

@[simp]
theorem checkRef_none_iff (st : State) (x : Ident)
: checkRef st x = .none <-> ∃ y, st.env x st.mem = .ok (.var y) := by
  unfold checkRef
  simp
  generalize st.env.lookup x st.mem = y
  cases y <;> simp
  rename_i y
  cases y <;> simp

theorem evalBinop_is_int (x y : Value) (op : Binop) (z : RValue)
                         (h : evalBinop x y op = .ok z)
: ∃ z', z = .int z' := by
  unfold evalBinop at h
  cases op <;> try simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  all_goals split at h <;> try simp at h
  all_goals split at h <;> try simp at h
  all_goals subst z; simp

theorem evalElem_wf (mem : Memory) (x y : Value) (z : RValue)
                    (h₁ : evalElem mem x y = .ok z)
                    (h₂ : mem.WF)
: z.WF mem := by
  unfold evalElem at h₁
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₁
  split at h₁ <;> try simp at h₁
  rename_i x' hx'
  split at h₁ <;> try simp at h₁
  rename_i y' hy'
  generalize hz : mem.mem x' = z' at h₁
  have := h₂.mem x'
  simp [hz] at this
  cases z' with
  | undefined => simp at h₁
  | closure => simp at h₁
  | arr xs =>
    simp at h₁ this
    apply this
    exact List.mem_of_getElem? h₁
  | sexp t xs =>
    simp at h₁ this
    apply this
    exact List.mem_of_getElem? h₁
  | str xs =>
    simp at h₁
    split at h₁ <;> try simp at h₁
    subst z
    simp

theorem evalElemRef_ok (x y : Value) (z : LValue)
                       (h : evalElemRef x y = .ok z)
: ∃ b i, z = .elem b i ∧ x = .rvalue (.box b) ∧ y = .rvalue (.int i) := by
  unfold evalElemRef at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  simp at *
  subst x y z
  simp [*]

theorem evalAssign_wf (st st' : State)
                      (x y : Value) (z : RValue)
                      (h₁ : st.WF) (h₂ : x.WF st) (h₃ : y.WF st)
                      (h₄ : evalAssign st x y = .ok (st', z))
: st'.WF ∧ y = .rvalue z := by
  unfold evalAssign at h₄
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₄
  split at h₄ <;> try simp at h₄
  rename_i hy
  simp at hy
  subst y
  split at h₄ <;> try simp at h₄
  rename_i hx
  obtain ⟨ rfl, rfl ⟩ := h₄
  simp
  unfold evalAssignR at hx
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at hx
  split at hx <;> try simp at hx
  rename_i hx'
  simp at hx'
  subst x
  split at hx <;> try simp at hx
  . simp at h₂ h₃
    split at hx <;> try simp at hx
    . subst hx
      simp [State.WF_iff]
      rename_i res h
      and_intros
      on_goal 2 =>
        apply Environment.assign_memory_wf at h
        . assumption
        . exact h₁.mem
        . assumption
      apply Environment.WF_transport st.mem
      . apply Environment.assign_memory_monotonic at h
        assumption
      . exact h₁.mem
      apply Environment.assign_wf at h
      . assumption
      . exact h₁.env
      . assumption
  . simp at h₂ h₃
    split at hx <;> try simp at hx
    rename_i h
    subst hx
    simp [State.WF_iff]
    and_intros
    . apply Environment.WF_transport st.mem
      on_goal 2 => apply h₁.mem
      on_goal 2 => apply h₁.env
      apply Memory.assign_monotonic
      apply BoxValue.assign_same_shape
      assumption
    apply Memory.assign_wf
    . exact h₁.mem
    . apply BoxValue.assign_wf at h
      . assumption
      . apply h₁.mem.mem
      . assumption
    . apply BoxValue.assign_same_shape at h
      assumption

abbrev prepareCallEnv (args : List (Ident × RValue))
                      (env : SimpleEnv)
: SimpleEnv :=
  List.foldl (fun acc (x, y) => acc.insert x (.var y)) env args

theorem prepareCallEnv_incl (args : List (Ident × RValue))
                            (env : SimpleEnv)
                            (x : Ident) (y : EnvValue)
                            (h : (prepareCallEnv args env).lookup x = .some y)
: env.lookup x = .some y ∨ ∃ y', y = .var y' ∧ (x, y') ∈ args := by
  induction args generalizing env with
  | nil =>
    simp at h
    simp [h]
  | cons arg args ih =>
    specialize ih _ h
    simp at ih
    obtain ih | ⟨ y, rfl, ih ⟩ := ih
    on_goal 2 =>
      right
      use y
      simp [ih]
    obtain ⟨ x', y' ⟩ := arg
    simp at ih
    by_cases hx : x = x'
    . subst x'
      simp at ih
      subst y
      simp
    rw [Finmap.lookup_insert_of_ne _ hx] at ih
    simp [ih]

theorem prepareCall_state_wf (mem : Memory) (x : Value) (xs : List RValue)
                             (st : State) (body : Expr)
                             (h₁ : mem.WF) (h₂ : ∀ x ∈ xs, x.WF mem)
                             (h₃ : prepareCall mem x xs = .ok (st, body))
: st.WF := by
  unfold prepareCall at h₃
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₃
  split at h₃ <;> try simp at h₃
  split at h₃ <;> try simp at h₃
  split_ifs at h₃
  simp at h₃
  obtain ⟨ rfl, rfl ⟩ := h₃
  simp [State.WF_iff, h₁]
  rename_i env params body _ _
  and_intros
  on_goal 2 => use env, params, body
  simp [SimpleEnv.WF]
  intro x' y' hy'
  apply prepareCallEnv_incl at hy'
  obtain hy' | ⟨ y'', rfl, hy' ⟩ := hy'
  . simp at hy'
  apply List.of_mem_zip at hy'
  exact h₂ _ hy'.2

theorem evalPattern_env_wf (mem : Memory) (x : RValue)
                           (p : Pattern) (env : SimpleEnv)
                           (h₁ : evalPattern mem x p = .some env)
                           (h₂ : mem.WF) (h₃ : x.WF mem)
: env.WF mem := by
  induction p
  using Pattern.rec (motive_2 := fun ps => (xs : List RValue) -> (env : SimpleEnv) -> evalPatternList mem xs ps = .some env -> (∀ x ∈ xs, x.WF mem) -> env.WF mem)
  generalizing x env with
  | wildcard =>
    simp at h₁
    subst env
    simp [SimpleEnv.WF]
  | const n =>
    simp at h₁
    obtain ⟨ rfl, rfl ⟩ := h₁
    simp [SimpleEnv.WF]
  | string s =>
    simp [Option.bind] at h₁
    split at h₁ <;> simp at h₁
    split at h₁ <;> simp at h₁
    obtain ⟨ rfl, rfl ⟩ := h₁
    simp [SimpleEnv.WF]
  | array ps ih =>
    simp [Option.bind] at h₁
    split at h₁ <;> simp at h₁
    rename_i x h
    simp at h
    subst h
    simp at h₃
    have := h₂.mem x
    split at h₁ <;> try simp at h₁
    rename_i xs h
    simp [h] at this
    apply ih at h₁
    apply h₁
    assumption
  | sexp t ps ih =>
    simp [Option.bind] at h₁
    split at h₁ <;> simp at h₁
    rename_i x h
    simp at h
    subst h
    simp at h₃
    have := h₂.mem x
    split at h₁ <;> try simp at h₁
    rename_i xs h
    simp [h] at this
    obtain ⟨ rfl, h₁ ⟩ := h₁
    apply ih at h₁
    apply h₁
    assumption
  | named xn p ih =>
    simp [Option.bind] at h₁
    split at h₁ <;> simp at h₁
    rename_i env h
    subst h₁
    apply ih at h
    specialize h h₃
    intro x' y' hy'
    by_cases hx' : x' = xn
    . subst x'
      simp at hy'
      subst y'
      simp [h₃]
    rw [Finmap.lookup_insert_of_ne _ hx'] at hy'
    apply h
    assumption
  | boxTag =>
    simp at h₁
    cases x <;> simp at h₁
    subst env
    simp [SimpleEnv.WF]
  | valTag =>
    simp at h₁
    cases x <;> simp at h₁
    subst env
    simp [SimpleEnv.WF]
  | strTag =>
    simp at h₁
    cases x <;> simp at h₁
    split at h₁ <;> simp at h₁
    subst env
    simp [SimpleEnv.WF]
  | sexpTag =>
    simp at h₁
    cases x <;> simp at h₁
    split at h₁ <;> simp at h₁
    subst env
    simp [SimpleEnv.WF]
  | arrayTag =>
    simp at h₁
    cases x <;> simp at h₁
    split at h₁ <;> simp at h₁
    subst env
    simp [SimpleEnv.WF]
  | funTag =>
    simp at h₁
    cases x <;> simp at h₁
    split at h₁ <;> simp at h₁
    subst env
    simp [SimpleEnv.WF]
  | nil xs env h₁ h₂ =>
    cases xs with
    | nil =>
      simp at h₁
      subst env
      simp [SimpleEnv.WF]
    | cons => simp at h₁
  | cons p ps ih₁ ih₂ xs env h₁ h₂ =>
    cases xs with
    | nil => simp at h₁
    | cons x xs =>
      simp [Option.bind] at h₁
      split at h₁ <;> simp at h₁
      rename_i env₁ henv₁
      split at h₁ <;> simp at h₁
      rename_i env₂ henv₂
      subst env
      apply ih₁ at henv₁
      apply ih₂ at henv₂
      simp [h₂] at henv₁ henv₂
      apply SimpleEnv.union_wf
      . apply henv₂
        intro x hx
        apply h₂
        simp [hx]
      . apply henv₁

theorem evalPatternList_env_wf (mem : Memory) (xs : List RValue)
                               (ps : List Pattern) (env : SimpleEnv)
                               (h₁ : evalPatternList mem xs ps = .some env)
                               (h₂ : mem.WF) (h₃ : ∀ x ∈ xs, x.WF mem)
: env.WF mem := by
  induction ps generalizing xs env with
  | nil =>
    cases xs with
    | nil =>
      simp at h₁
      subst env
      simp [SimpleEnv.WF]
    | cons => simp at h₁
  | cons p ps ih =>
    cases xs with
    | nil => simp at h₁
    | cons x xs =>
      simp [Option.bind] at h₁
      split at h₁ <;> simp at h₁
      rename_i env₁ henv₁
      split at h₁ <;> simp at h₁
      rename_i env₂ henv₂
      subst env
      apply evalPattern_env_wf at henv₁
      apply ih at henv₂
      simp [h₂] at henv₁ henv₂
      apply SimpleEnv.union_wf
      . apply henv₂
        intro x hx
        apply h₃
        simp [hx]
      . apply henv₁
        apply h₃
        simp

theorem chooseCaseR_env_wf (mem : Memory) (x : RValue)
                           (bs : List (Pattern × Expr))
                           (env : SimpleEnv) (body : Expr)
                           (h₁ : chooseCaseR mem x bs = .some (env, body))
                           (h₂ : mem.WF) (h₃ : x.WF mem)
: env.WF mem := by
  fun_induction chooseCaseR generalizing env body with
  | case1 => simp at h₁
  | case2 p e bs env h =>
    simp at h₁
    obtain ⟨ rfl, rfl ⟩ := h₁
    apply evalPattern_env_wf at h
    apply h <;> assumption
  | case3 p e bs h ih =>
    apply ih at h₁
    assumption

theorem chooseCase_env_wf (st : State) (x : Value)
                          (bs : List (Pattern × Expr))
                          (env : SimpleEnv) (body : Expr)
                          (h₁ : chooseCase st.mem x bs = .ok (env, body))
                          (h₂ : st.mem.WF) (h₃ : x.WF st)
: env.WF st.mem := by
  unfold chooseCase at h₁
  simp [Bind.bind, Except.bind] at h₁
  split at h₁ <;> try simp at h₁
  apply chooseCaseR_env_wf at h₁
  apply h₁
  . assumption
  rename_i x hx
  simp at hx
  subst hx
  exact h₃

theorem prepareDefList_env_wf (mem : Memory) (defs : List Definition)
                              (env : SimpleEnv) (body : Expr)
                              (h : prepareDefList defs = (env, body))
: env.WF mem := by
  fun_induction prepareDefList generalizing env body with
  | case1 =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp [SimpleEnv.WF]
  | case2 x y ds env e h₁ env' ih =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    specialize ih _ _ h₁
    subst env'
    split_ifs with h₂
    . apply ih
    intro x' y' hy'
    by_cases hx' : x' = x
    . subst x'
      simp at hy'
      subst y'
      simp
    rw [Finmap.lookup_insert_of_ne _ hx'] at hy'
    apply ih
    assumption
  | case3 x xs body ds env e h₁ env' ih =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    specialize ih _ _ h₁
    subst env'
    split_ifs with h₂
    . apply ih
    intro x' y' hy'
    by_cases hx' : x' = x
    . subst x'
      simp at hy'
      subst y'
      simp
    rw [Finmap.lookup_insert_of_ne _ hx'] at hy'
    apply ih
    assumption

theorem Eval_result_wf (st : State) (e : Expr) (r : Result Value)
                       (h₁ : st.WF) (h₂ : Eval st e r)
: r.WF (fun x st => x.WF st) := by
  induction h₂
  using Eval.rec (motive_2 := fun st es r _ => st.WF -> r.WF (fun xs st => ∀ x ∈ xs, x.WF st.mem))
  with
  | skip => simp [h₁]
  | varOk st st' x y h =>
    apply evalVar_wf at h
    . exact h
    . exact h₁
  | varErr => simp
  | refOk st x h =>
    simp at h
    simp [h, h₁]
  | refErr => simp
  | int => simp [h₁]
  | str st st' s box h₂ =>
    apply State.allocWith_wf at h₂
    . assumption
    . assumption
    . simp
    . simp
  | arrOk st₁ st₂ st₃ xs ys box h₂ h₃ ih =>
    specialize ih h₁
    simp at ih
    apply State.allocWith_wf at h₃
    . assumption
    . exact ih.2
    . exact ih.1
    . simp
  | arrErr => simp
  | sexpOk st₁ st₂ st₃ t xs ys box h₂ h₃ ih =>
    specialize ih h₁
    simp at ih
    apply State.allocWith_wf at h₃
    . assumption
    . exact ih.2
    . exact ih.1
    . simp
  | sexpErr => simp
  | lambdaOk st₁ st₂ xs x box env h₂ h₃ =>
    apply Environment.close_wf at h₂
    on_goal 2 => exact h₁.mem
    on_goal 2 => exact h₁.env
    apply State.allocWith_wf at h₃
    . assumption
    . assumption
    . simp [h₂]
    . simp
  | lambdaErr => simp
  | binopOk st₁ st₂ st₃ op x₁ x₂ y₁ y₂ z h₂ h₃ h₄ ih₁ ih₂ =>
    apply evalBinop_is_int at h₄
    obtain ⟨ z, rfl ⟩ := h₄
    simp
    specialize ih₁ h₁
    specialize ih₂ ih₁.2
    simp at ih₁ ih₂
    simp [ih₂]
  | binopErr => simp
  | binopErrL => simp
  | binopErrR => simp
  | elemOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₂ h₃ h₄ ih₁ ih₂ =>
    specialize ih₁ h₁
    specialize ih₂ ih₁.2
    simp at ih₁ ih₂ ⊢
    simp [ih₂]
    apply evalElem_wf at h₄
    apply h₄
    exact ih₂.2.mem
  | elemErr => simp
  | elemErrL => simp
  | elemErrR => simp
  | elemRefOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₂ h₃ h₄ ih₁ ih₂ =>
    specialize ih₁ h₁
    specialize ih₂ ih₁.2
    simp at ih₁ ih₂ ⊢
    simp [ih₂]
    apply evalElemRef_ok at h₄
    obtain ⟨ b, i, rfl, rfl, rfl ⟩ := h₄
    simp at *
    apply Eval_state_monotonic at h₃
    grw [<-h₃.mem.bound]
    exact ih₁.1
  | elemRefErr => simp
  | elemRefErrL => simp
  | elemRefErrR => simp
  | callOk st₁ st₂ st₃ st₄ st₅ x xs y ys z z' h₁ h₂ h₃ h₄ ih₁ ih₂ ih₃ =>
    simp at ih₁ ih₂ ih₃
    unfold commitCall
    cases z' <;> simp
    rename_i z'
    specialize ih₁ h₁
    specialize ih₂ ih₁.2
    have := prepareCall_state_wf _ _ _ _ _ ih₂.2.mem ih₂.1 h₃
    specialize ih₃ this
    simp at ih₃
    simp [ih₃.1, State.WF_iff, ih₃.2.mem]
    apply Environment.WF_transport st₃.mem
    on_goal 2 => exact ih₂.2.mem
    on_goal 2 => exact ih₂.2.env
    apply prepareCall_state at h₃
    rw [h₃]
    apply Eval_state_monotonic at h₄
    exact h₄.mem
  | callErr₁ => simp
  | callErr₂ => simp
  | callErr₃ => simp
  | callErr₄ => simp
  | assignOk st₁ st₂ st₃ st₄ x₁ x₂ y₁ y₂ z h₂ h₃ h₄ ih₁ ih₂ =>
    specialize ih₁ h₁
    specialize ih₂ ih₁.2
    simp at ih₁ ih₂ ⊢
    have h₅ := evalAssign_state_monotonic (h := h₄)
    apply evalAssign_wf at h₄
    on_goal 2 => simp [ih₂]
    on_goal 3 => simp [ih₂]
    on_goal 2 =>
      apply Value.WF_transport
      . exact ih₁.2
      on_goal 2 => exact ih₁.1
      apply Eval_state_monotonic
      exact h₃
    obtain ⟨ h₄, rfl ⟩ := h₄
    simp at ih₂
    simp [h₄]
    apply RValue.WF_transport
    . exact h₅.mem
    . exact ih₂.1
  | assignErr => simp
  | assignErrL => simp
  | assignErrR => simp
  | seqOk st₁ st₂ x₁ x₂ y₁ res h₁ h₂ ih₁ ih₂ =>
    specialize ih₁ h₁
    apply ih₂ ih₁.2
  | seqErr => simp
  | iteThen st st' x₁ x₂ x₃ y₁ res h₂ h₃ h₄ ih₁ ih₂ =>
    specialize ih₁ h₁
    apply ih₂ ih₁.2
  | iteElse st st' x₁ x₂ x₃ y₁ res h₂ h₃ h₄ ih₁ ih₂ =>
    specialize ih₁ h₁
    apply ih₂ ih₁.2
  | iteErr₁ => simp
  | iteErr₂ => simp
  | loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res h₂ h₃ h₄ h₅ ih₁ ih₂ ih₃ =>
    specialize ih₁ h₁
    specialize ih₂ ih₁.2
    apply ih₃ ih₂.2
  | loopStop st st' x₁ x₂ y₁ h₂ h₃ ih =>
    specialize ih h₁
    simp [ih.2]
  | loopErr => simp
  | loopErrL => simp
  | loopErrR => simp
  | caseOk st₁ st₂ x₁ bs y₁ env x₂ res h₂ h₃ h₄ ih₁ ih₂ =>
    apply Result.popEnv_wf
    specialize ih₁ h₁
    simp at ih₁
    apply ih₂
    simp [State.WF_iff, ih₁.2.mem, ih₁.2.env]
    apply chooseCase_env_wf at h₃
    apply h₃
    . exact ih₁.2.mem
    . exact ih₁.1
  | caseErr₁ => simp
  | caseErr₂ => simp
  | scope st x₁ env x₂ res h₂ h₃ ih =>
    apply Result.popEnv_wf
    apply ih
    simp [State.WF_iff, h₁.mem, h₁.env]
    apply prepareDefList_env_wf at h₂
    exact h₂
  | nil st h => simp [h]
  | cons st₁ st₂ st₃ x xs y ys h₂ h₃ ih₁ ih₂ h =>
    simp at ih₁ ih₂ ⊢
    apply ih₁ at h
    obtain ⟨ h₁, h ⟩ := h
    apply ih₂ at h
    and_intros
    on_goal 2 => exact h.1
    on_goal 2 => exact h.2
    apply RValue.WF_transport st₂.mem
    on_goal 2 => assumption
    apply EvalList_state_monotonic at h₃
    exact h₃.mem
  | err => simp
  | errL => simp
  | errR => simp

theorem EvalList_result_wf (st : State) (es : List Expr)
                           (r : Result (List RValue))
                           (h₁ : st.WF) (h₂ : EvalList st es r)
: r.WF (fun xs st => ∀ x ∈ xs, x.WF st.mem) := by
  induction es generalizing st r with
  | nil =>
    cases h₂ with
    | nil => simp [h₁]
  | cons e es ih =>
    cases h₂ with
    | cons _ st₂ st₃ _ _ x xs h₂ h₃ =>
      apply Eval_result_wf at h₂
      on_goal 2 => assumption
      simp at h₂
      have := h₃
      apply ih at h₃
      on_goal 2 => exact h₂.2
      simp at h₃
      simp
      and_intros
      . apply EvalList_state_monotonic at this
        apply RValue.WF_transport
        . apply this.mem
        . exact h₂.1
      . exact h₃.1
      . exact h₃.2
    | err => simp
    | errL => simp
    | errR => simp
