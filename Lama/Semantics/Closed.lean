import Mathlib.Tactic.ApplyFun

import Lama.Ast.Closed
import Lama.Semantics.WellFormed


attribute [simp] Finmap.notMem_empty

namespace Finmap

variable {α : Type u} {β : α -> Type v} {γ : α -> Type w}
         (f : (x : α) -> β x -> γ x)

@[reducible]
def map (xs : Finmap β) : Finmap γ where
  entries := xs.entries.map (fun x => ⟨ x.1, f x.1 x.2 ⟩)
  nodupKeys := by
    rw [<-Multiset.nodup_keys]
    simp [Multiset.keys]
    change xs.entries.keys.Nodup
    rw [Multiset.nodup_keys]
    exact xs.nodupKeys

@[simp]
theorem map_empty : map f ∅ = ∅ := by
  ext
  simp [show (∅ : Finmap β).entries = ∅ by rfl, show (∅ : Finmap γ).entries = ∅ by rfl]

@[simp]
theorem lookup_map [DecidableEq α] (x : α) (xs : Finmap β)
: (xs.map f).lookup x = (xs.lookup x).map (f x) := by
  cases hx : xs.lookup x with
  | none =>
    simp
    rw [lookup_eq_none] at hx ⊢
    contrapose! hx
    change x ∈ (map f xs).keys at hx
    change x ∈ xs.keys
    simp [Finmap.keys, Multiset.keys] at *
    exact hx
  | some y =>
    simp
    rw [lookup_eq_some_iff] at hx ⊢
    simp
    use x, y

@[simp]
theorem mem_map [DecidableEq α] (x : α) (xs : Finmap β)
: x ∈ xs.map f <-> x ∈ xs := by
  rw [Finmap.mem_iff, Finmap.mem_iff]
  simp only [Finmap.lookup_map, Option.map_eq_some_iff]
  constructor <;> intro h
  . obtain ⟨ -, y, h, - ⟩ := h
    use y
  . obtain ⟨ y, h ⟩ := h
    use f x y, y

@[simp]
theorem map_union [DecidableEq α] (xs ys : Finmap β)
: (xs ∪ ys).map f = xs.map f ∪ ys.map f := by
  apply Finmap.ext_lookup
  intro x
  simp
  by_cases hx : x ∈ xs
  . rw [Finmap.lookup_union_left]
    on_goal 2 => assumption
    rw [Finmap.lookup_union_left]
    on_goal 2 => simp [hx]
    simp
  . rw [Finmap.lookup_union_right]
    on_goal 2 => assumption
    rw [Finmap.lookup_union_right]
    on_goal 2 => simp [hx]
    simp

@[simp]
theorem map_insert [DecidableEq α] (xs : Finmap β) (x : α) (y : β x)
: (xs.insert x y).map f = (xs.map f).insert x (f x y) := by
  apply Finmap.ext_lookup
  intro x'
  simp
  by_cases hx' : x' = x
  . subst x'
    simp
  simp [hx']

end Finmap

namespace Lama.Semantics

open Ast

@[simp]
theorem Context.addVars_app (ctx : Context) (xs ys : List Ident)
: (ctx.addVars xs).addVars ys = ctx.addVars (xs ++ ys) := by
  fun_induction Context.addVars with
  | case1 => simp
  | case2 ctx x xs ih => simp [ih]

theorem Context.addVars_perm (ctx : Context) (xs ys : List Ident)
                             (h : xs.Perm ys)
: ctx.addVars xs = ctx.addVars ys := by
  induction h generalizing ctx with
  | nil => simp
  | cons x h ih => simp [ih]
  | swap x y xs =>
    simp
    congr 1
    apply Finmap.ext_lookup
    intro z
    by_cases hzx : z = x <;> by_cases hzy : z = y
    . subst z y
      simp
    . subst z
      simp [Finmap.lookup_insert_of_ne _ hzy]
    . subst z
      simp [Finmap.lookup_insert_of_ne _ hzx]
    . simp [Finmap.lookup_insert_of_ne _ hzx, Finmap.lookup_insert_of_ne _ hzy]
  | trans h₁ h₂ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem Context.lookup_addVars (ctx : Context) (xs : List Ident)
                               (x : Ident) (y : Bool)
: (ctx.addVars xs).lookup x = .some y <-> x ∈ xs ∧ y = true ∨ x ∉ xs ∧ ctx.lookup x = .some y where
  mp h := by
    fun_induction Context.addVars with
    | case1 ctx => simp [h]
    | case2 ctx x' xs ih =>
      simp [h] at ih
      obtain ⟨ ih, rfl ⟩ | ih := ih
      . simp [ih]
      by_cases hx' : x = x'
      . subst x
        simp at ih
        simp [ih]
      rw [Finmap.lookup_insert_of_ne _ hx'] at ih
      simp [ih, hx']
  mpr h := by
    fun_induction Context.addVars with
    | case1 ctx =>
      simp at h
      assumption
    | case2 ctx x' xs ih =>
      apply ih
      clear ih
      simp at h
      obtain ⟨ rfl | h, rfl ⟩ | ⟨ ⟨ h₁, h₂ ⟩, h₃ ⟩ := h
      . simp
        tauto
      . simp [h]
      . simp [h₁, h₂, h₃]

@[simp]
theorem Context.union_addVars_empty (ctx : Context) (xs : List Ident)
: Context.addVars ∅ xs ∪ ctx = ctx.addVars xs := by
  apply Finmap.ext_lookup
  intro x
  generalize h : (ctx.addVars xs).lookup x = y
  cases y
  . contrapose! h
    simp only [Ne, Option.eq_none_iff_forall_ne_some, Context.lookup_addVars] at *
    contrapose! h
    intro y
    specialize h y
    obtain ⟨ h₁, h₂ ⟩ := h
    by_cases hx : x ∈ xs
    . simp [hx] at h₁
      subst h₁
      simp [hx]
      intro hx'
      apply h₂
      contrapose! hx'
      rw [Finmap.mem_iff]
      simp [hx']
    . simp [hx] at h₂
      simp [hx, h₂]
  . rename_i y
    simp at *
    obtain ⟨ h, rfl ⟩ | ⟨ h₁, h₂ ⟩ := h
    . simp [h]
    rw [Finmap.mem_iff]
    simp [h₁, h₂]

@[reducible]
def EnvValue.isVar
: EnvValue -> Bool
| var _ => true
| fn _ _ => false

theorem EnvValue.isVar_transport (x y : EnvValue)
                                 (h : x.SameShape y)
: x.isVar = y.isVar := by
  cases x <;> simp at h
  . obtain ⟨ y', rfl ⟩ := h
    simp
  . subst h
    simp

def EnvValue.IsClosed (ctx : Context)
: EnvValue -> Prop
| var _ => True
| fn params body => body.IsClosed (ctx.addVars params)

@[simp]
theorem EnvValue.IsClosed_var (ctx : Context) (x : RValue)
: (var x).IsClosed ctx := True.intro

@[simp]
theorem EnvValue.IsClosed_fn (ctx : Context)
                             (params : List Ident)
                             (body : Expr)
: (fn params body).IsClosed ctx <-> body.IsClosed (ctx.addVars params) := by rfl

theorem EnvValue.IsClosed_transport (ctx : Context)
                                    (x y : EnvValue)
                                    (h : x.SameShape y)
: x.IsClosed ctx <-> y.IsClosed ctx := by
  cases x <;> simp at h
  . obtain ⟨ y', rfl ⟩ := h
    simp
  subst h
  simp

def SimpleEnv.IsClosed (ctx : Context) (env : SimpleEnv) : Prop :=
  ∀ x y, env.lookup x = .some y -> y.IsClosed ctx

theorem SimpleEnv.IsClosed_transport (ctx : Context)
                                     (env env' : SimpleEnv)
                                     (h : env.SameShape env')
: env.IsClosed ctx <-> env'.IsClosed ctx := by
  revert env env' h
  suffices (env env' : SimpleEnv) -> env'.SameShape env -> env.IsClosed ctx -> env'.IsClosed ctx by
    intro env env' h
    constructor <;> intro h' <;> refine this _ _ ?_ h'
    . symm
      assumption
    . assumption
  intro env env' h₁ h₂ x y₁ h₃
  specialize h₁ x
  simp [h₃] at h₁
  obtain ⟨ y₂, h₁, h₄ ⟩ := h₁
  apply h₂ at h₁
  rw [EnvValue.IsClosed_transport]
  . exact h₁
  . assumption

abbrev SimpleEnv.context (env : SimpleEnv) : Context :=
  env.map fun _ x => x.isVar

theorem SimpleEnv.context_transport (env env' : SimpleEnv)
                                    (h : env.SameShape env')
: env.context = env'.context := by
  apply Finmap.ext_lookup
  intro x
  simp [Option.map]
  replace h := h x
  generalize env.lookup x = y₁ at *
  cases y₁ <;> simp at h ⊢
  . simp [h]
  rename_i y₁
  obtain ⟨ y₂, h₁, h₂ ⟩ := h
  simp [h₁]
  apply EnvValue.isVar_transport
  assumption

@[reducible, simp]
def ClosedEnv.context
: ClosedEnv -> Context
| empty => ∅
| scope xs env => xs.context ∪ env.context

theorem ClosedEnv.context_transport (env env' : ClosedEnv)
                                    (h : env.SameShape env')
: env.context = env'.context := by
  fun_induction SameShape with
  | case1 => simp
  | case2 xs₁ env₁ xs₂ env₂ ih =>
    simp [h] at ih
    simp [ih]
    congr 1
    apply SimpleEnv.context_transport
    simp [h]
  | case3 => simp at h

@[reducible, simp]
def ClosedEnv.IsClosed
: ClosedEnv -> Prop
| empty => True
| scope xs env =>
  xs.IsClosed (scope xs env).context ∧ env.IsClosed

theorem ClosedEnv.IsClosed_transport (env env' : ClosedEnv)
                                     (h : env.SameShape env')
: env.IsClosed <-> env'.IsClosed := by
  fun_induction SameShape with
  | case1 => simp
  | case2 xs₁ env₁ xs₂ env₂ ih =>
    simp [h] at ih
    simp
    rw [
      ih,
      SimpleEnv.context_transport _ _ h.1,
      ClosedEnv.context_transport _ _ h.2,
      SimpleEnv.IsClosed_transport _ _ _ h.1,
    ]
  | case3 => simp at h

@[reducible]
def EnvLookup.isVar
: EnvLookup -> Bool
| var _ => true
| fn _ _ _ => false

@[simp]
theorem EnvValue.toLookup_isVar (x : EnvValue) (env : ClosedEnv)
: (x.toLookup env).isVar = x.isVar := by
  cases x <;> simp [toLookup]

theorem ClosedEnv.lookup_fn_closed (env env' : ClosedEnv) (x : Ident)
                                   (params : List Ident) (body : Expr)
                                   (h₁ : env.IsClosed)
                                   (h₂ : env.lookup x = .some (.fn env' params body))
: env'.IsClosed ∧ body.IsClosed (env'.context.addVars params) := by
  fun_induction lookup with
  | case1 => simp at h₂
  | case2 xs env y h =>
    cases y <;> simp at h₂
    obtain ⟨ rfl, rfl, rfl ⟩ := h₂
    simp [h₁]
    simp at h₁
    have := h₁.1 _ _ h
    simp at this
    assumption
  | case3 xs env h ih =>
    simp [h₁.2, h₂] at ih
    assumption

def BoxValue.IsClosed : BoxValue -> Prop
| closure env params body =>
  env.IsClosed ∧ body.IsClosed (env.context.addVars params)
| _ => True

@[simp]
theorem BoxValue.IsClosed_undefined
: undefined.IsClosed := True.intro

@[simp]
theorem BoxValue.IsClosed_str (xs : ByteArray)
: (str xs).IsClosed := True.intro

@[simp]
theorem BoxValue.IsClosed_arr (xs : List RValue)
: (arr xs).IsClosed := True.intro

@[simp]
theorem BoxValue.IsClosed_sexp (t : Tag) (xs : List RValue)
: (sexp t xs).IsClosed := True.intro

@[simp]
theorem BoxValue.IsClosed_closure (env : ClosedEnv) (params : List Ident) (body : Expr)
: (closure env params body).IsClosed <-> env.IsClosed ∧ body.IsClosed (env.context.addVars params) := by rfl

theorem BoxValue.IsClosed_transport (x y : BoxValue)
                                    (h : x.SameShape y)
: x.IsClosed <-> y.IsClosed := by
  cases x with
  | undefined =>
    simp at h
    subst h
    simp
  | str xs =>
    simp at h
    obtain ⟨ ys, rfl, h ⟩ := h
    simp
  | arr xs =>
    simp at h
    obtain ⟨ ys, rfl, h ⟩ := h
    simp
  | sexp t xs =>
    simp at h
    obtain ⟨ ys, rfl, h ⟩ := h
    simp
  | closure env params body =>
    simp at h
    obtain ⟨ env', rfl, h ⟩ := h
    simp
    rw [ClosedEnv.context_transport _ _ h]
    rw [ClosedEnv.IsClosed_transport _ _ h]

theorem BoxValue.assign_closed (x z : BoxValue) (i : ℕ) (y : RValue)
                               (h : x.assign i y = .ok z)
: z.IsClosed := by
  unfold assign at h
  cases x with
  | undefined => simp at h
  | str xs =>
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    subst h
    simp
  | arr xs =>
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h <;> try simp at h
    subst h
    simp
  | sexp t xs =>
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h <;> try simp at h
    subst h
    simp
  | closure => simp at h

def Memory.IsClosed (m : Memory) : Prop :=
  ∀ b, (m b).IsClosed

theorem Memory.alloc_memory_closed (mem mem' : Memory) (box : Box)
                                   (h₁ : mem.IsClosed)
                                   (h₂ : mem.alloc = (box, mem'))
: mem'.IsClosed := by
  simp at h₂
  obtain ⟨ rfl, rfl ⟩ := h₂
  exact h₁

theorem Memory.assign_closed (mem : Memory) (x : BoxValue) (box : Box)
                             (h₁ : mem.IsClosed) (h₂ : x.IsClosed)
: (mem.assign box x).IsClosed := by
  intro b
  simp
  split_ifs with hb
  . subst b
    assumption
  . apply h₁

theorem Memory.allocWith_memory_closed (mem mem' : Memory)
                                       (x : BoxValue) (box : Box)
                                       (h₁ : mem.IsClosed) (h₂ : x.IsClosed)
                                       (h₃ : mem.allocWith x = (box, mem'))
: mem'.IsClosed := by
  unfold allocWith at h₃
  split at h₃
  obtain ⟨ rfl, rfl ⟩ := h₃
  rename_i h
  apply alloc_memory_closed at h
  on_goal 2 => assumption
  apply Memory.assign_closed <;> assumption

@[reducible, simp]
def Environment.context (mem : Memory)
: Environment -> Context
| empty => ∅
| closure box =>
  match mem box with
  | .closure xs _ _ => xs.context
  | _ => ∅
| scope xs env => xs.context ∪ env.context mem

theorem Environment.context_transport (mem mem' : Memory)
                                      (env env' : Environment)
                                      (h₁ : mem.WF) (h₂ : env.WF mem)
                                      (h₃ : mem ≤ mem') (h₄ : env.SameShape env')
: env.context mem = env'.context mem' := by
induction env generalizing env' with
| empty =>
  simp at h₄
  subst h₄
  simp
| closure box =>
  simp at h₄
  subst h₄
  obtain ⟨ env, params, body, h₂ ⟩ := h₂
  have := h₁.bound box
  simp [h₂] at this
  replace this := h₃.vals box this
  simp [h₂] at this
  obtain ⟨ env', h₃, h₄ ⟩ := this
  simp [h₂, h₃]
  apply ClosedEnv.context_transport
  assumption
| scope xs env ih =>
  simp at h₂ h₄
  obtain ⟨ xs', env', rfl, h₄ ⟩ := h₄
  simp
  congr 1
  . apply SimpleEnv.context_transport
    exact h₄.1
  apply ih
  . exact h₂.2
  . exact h₄.2

@[reducible, simp]
def Environment.IsClosed (mem : Memory)
: Environment -> Prop
| empty => True
| closure _ => True
| scope xs env =>
  xs.IsClosed ((scope xs env).context mem) ∧ env.IsClosed mem

theorem Environment.IsClosed_transport (mem mem' : Memory)
                                       (env env' : Environment)
                                       (h₁ : mem.WF) (h₂ : env.WF mem)
                                       (h₃ : mem ≤ mem') (h₄ : env.SameShape env')
                                       (h₅ : env.IsClosed mem)
: env'.IsClosed mem' := by
  induction env generalizing env' with
  | empty =>
    simp at h₄
    subst h₄
    simp
  | closure =>
    simp at h₄
    subst h₄
    simp
  | scope xs env ih =>
    simp at h₂ h₄ h₅
    simp [h₂, h₅] at ih
    obtain ⟨ xs', env', rfl, h₄ ⟩ := h₄
    simp
    and_intros
    on_goal 2 =>
      apply ih
      simp [h₄]
    rw [<- SimpleEnv.context_transport xs] <;> try simp [*]
    rw [<- Environment.context_transport mem _ env] <;> try simp [*]
    rw [<- SimpleEnv.IsClosed_transport]
    . exact h₅.1
    . exact h₄.1

theorem Environment.close_context (mem : Memory) (env : Environment) (env' : ClosedEnv)
                                  (h : env.close mem = .some env')
: env'.context = env.context mem := by
  fun_induction close generalizing env' with
  | case1 =>
    simp at h
    subst h
    simp
  | case2 b xs params body h =>
    simp at h
    subst h
    simp [h]
  | case3 => simp at h
  | case4 xs env ih =>
    simp [Option.bind] at h
    split at h <;> simp at h
    subst h
    rename_i xs' h
    specialize ih _ h
    simp [ih]

theorem Environment.close_closed (mem : Memory) (env : Environment) (env' : ClosedEnv)
                                 (h₁ : mem.IsClosed) (h₂ : env.IsClosed mem)
                                 (h₃ : env.close mem = .some env')
: env'.IsClosed := by
  fun_induction close generalizing env' with
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
    simp at h₂
    specialize ih _ ?_ h
    . simp [h₂]
    simp [ih]
    apply close_context at h
    simp [h, h₂]

theorem Environment.lookup_fn_closed (mem : Memory) (env : Environment) (x : Ident)
                                     (env' : ClosedEnv) (params : List Ident) (body : Expr)
                                     (h₁ : mem.IsClosed) (h₂ : env.IsClosed mem)
                                     (h₃ : env.lookup x mem = .ok (.fn env' params body))
: env'.IsClosed ∧ body.IsClosed (env'.context.addVars params) := by
  fun_induction lookup with
  | case1 => simp at h₃
  | case2 box env params' body' h =>
    simp at h₃
    apply ClosedEnv.lookup_fn_closed at h₃
    . assumption
    specialize h₁ box
    simp [h] at h₁
    simp [h₁]
  | case3 => simp at h₃
  | case4 xs env y h =>
    simp [Functor.map, Except.map] at h₃
    split at h₃ <;> simp at h₃
    rename_i env' h'
    simp [Option.bind] at h'
    split at h' <;> simp at h'
    subst h'
    rename_i env' h'
    cases y <;> simp at h₃
    obtain ⟨ rfl, rfl, rfl ⟩ := h₃
    simp
    rw [Environment.close_context _ _ _ h']
    simp at h₂
    apply Environment.close_closed at h'
    on_goal 2 => assumption
    on_goal 2 => simp [h₂]
    have := h₂.1 _ _ h
    simp at this
    simp [h', h₂, this]
  | case5 xs env h ih =>
    apply ih
    . exact h₂.2
    . assumption

theorem Environment.assign_memory_closed (mem mem' : Memory)
                                         (env env' : Environment)
                                         (x : Ident) (y : RValue)
                                         (h₁ : mem.IsClosed)
                                         (h₂ : env.assign x y mem = .ok (env', mem'))
: mem'.IsClosed := by
  fun_induction assign generalizing env' with
  | case1 => simp at h₂
  | case2 box env params body h =>
    simp [Functor.map, Except.map] at h₂
    split at h₂ <;> simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    rename_i env' h₂
    simp at h₂
    apply Memory.assign_closed
    . assumption
    simp
    have := h₁ box
    simp [h] at this
    apply ClosedEnv.assign_same_shape at h₂
    rw [<- ClosedEnv.IsClosed_transport env]
    rw [<- ClosedEnv.context_transport env]
    . exact this
    . assumption
    . assumption
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
    rename_i res h
    apply ih
    assumption

structure State.IsClosed (st : State) : Prop where
  mem : st.mem.IsClosed
  env : st.env.IsClosed st.mem

theorem State.IsClosed_iff (st : State)
: st.IsClosed <-> st.mem.IsClosed ∧ st.env.IsClosed st.mem where
  mp h := by
    obtain ⟨ h₁, h₂ ⟩ := h
    exact ⟨ h₁, h₂ ⟩
  mpr h := by
    obtain ⟨ h₁, h₂ ⟩ := h
    exact ⟨ h₁, h₂ ⟩

theorem State.allocWith_closed (st st' : State)
                               (x : BoxValue) (box : Box)
                               (h₁ : st.WF) (h₂ : st.IsClosed) (h₃ : x.IsClosed)
                               (h₄ : st.allocWith x = (box, st'))
: st'.IsClosed := by
  unfold allocWith at h₄
  split at h₄
  simp at h₄
  obtain ⟨ rfl, rfl ⟩ := h₄
  rename_i mem' h
  simp [IsClosed_iff]
  and_intros
  . apply Memory.allocWith_memory_closed <;> try assumption
    exact h₂.mem
  apply Memory.allocWith_monotonic at h
  rw [WF_iff] at h₁
  rw [IsClosed_iff] at h₂
  apply Environment.IsClosed_transport st.mem _ st.env <;> simp [*]

abbrev State.context (st : State) : Context :=
  st.env.context st.mem

theorem State.context_transport (st st' : State)
                                (h₁ : st.WF) (h₂ : st ≤ st')
: st.context = st'.context := by
  rw [WF_iff] at h₁
  rw [LE_iff] at h₂
  apply Environment.context_transport <;> simp [*]

theorem evalVar_state_closed (st st' : State)
                             (x : Ident) (y : RValue)
                             (h₁ : st.WF) (h₂ : st.IsClosed)
                             (h₃ : evalVar st x = .ok (y, st'))
: st'.IsClosed := by
  unfold evalVar at h₃
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₃
  split at h₃ <;> try simp at h₃
  rename_i y hy
  split at h₃ <;> try simp at h₃
  . obtain ⟨ rfl, rfl ⟩ := h₃
    assumption
  rename_i env params body
  obtain ⟨ rfl, rfl ⟩ := h₃
  apply State.allocWith_closed (h₄ := rfl)
  . assumption
  . assumption
  simp [State.IsClosed_iff] at h₂
  apply Environment.lookup_fn_closed at hy <;> simp [*]

@[simp]
theorem prepareCallEnv_context (args : List (Ident × RValue)) (env : SimpleEnv)
: (prepareCallEnv args env).context = env.context.addVars (args.map (·.1)) := by
  unfold prepareCallEnv
  induction args generalizing env with
  | nil => simp
  | cons a args ih => simp [ih]

theorem prepareCall_env_closed (mem : Memory) (x : Value) (xs : List RValue)
                               (st : State) (y : Expr)
                               (h : prepareCall mem x xs = .ok (st, y))
: st.env.IsClosed mem := by
  unfold prepareCall at h
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp at h
  rename_i box h'
  simp at h'
  subst h'
  split at h <;> try simp at h
  rename_i env params body h₁
  split_ifs at h with h₂
  simp at h h₂
  obtain ⟨ rfl, rfl ⟩ := h
  simp [h₁]
  change SimpleEnv.IsClosed _ (prepareCallEnv _ _)
  intro x' y' hx'
  suffices y'.isVar by
    cases y' <;> simp at this
    simp
  have := prepareCallEnv_context (params.zip xs) ∅
  apply_fun Finmap.lookup x' at this
  rw [List.map_fst_zip h₂] at this
  simp [-prepareCallEnv_context, hx'] at this
  symm at this
  simp at this
  simp [this]

theorem prepareCall_expr_closed (mem : Memory) (x : Value) (xs : List RValue)
                                (st : State) (y : Expr)
                                (h₁ : mem.IsClosed)
                                (h₂ : prepareCall mem x xs = .ok (st, y))
: y.IsClosed st.context := by
  unfold prepareCall at h₂
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₂
  split at h₂ <;> try simp at h₂
  rename_i box h
  simp at h
  subst h
  split at h₂ <;> try simp at h₂
  rename_i env params body h
  split_ifs at h₂ with h'
  simp at h' h₂
  obtain ⟨ rfl, rfl ⟩ := h₂
  specialize h₁ box
  simp [h] at h₁
  simp [State.context, h, List.map_fst_zip h', h₁]

theorem evalAssign_state_closed (st st' : State)
                                (x y : Value) (z : RValue)
                                (h₁ : st.WF) (h₂ : st.IsClosed)
                                (h₃ : evalAssign st x y = .ok (st', z))
: st'.IsClosed := by
  unfold evalAssign at h₃
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₃
  split at h₃ <;> try simp at h₃
  rename_i y h
  simp at h
  subst h
  split at h₃ <;> simp at h₃
  obtain ⟨ rfl, rfl ⟩ := h₃
  rename_i st' h₃
  unfold evalAssignR at h₃
  simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h₃
  split at h₃ <;> try simp at h₃
  rename_i x h
  simp at h
  subst h
  cases x with
  | var x =>
    simp at h₃
    split at h₃ <;> simp at h₃
    subst h₃
    rename_i res h
    simp [State.IsClosed_iff]
    and_intros
    . apply Environment.assign_memory_closed at h
      . assumption
      . exact h₂.mem
    apply Environment.IsClosed_transport
    . exact h₁.mem
    . exact h₁.env
    . apply Environment.assign_memory_monotonic at h
      assumption
    . apply Environment.assign_same_shape at h
      assumption
    . exact h₂.env
  | elem b i =>
    simp at h₃
    split at h₃ <;> simp at h₃
    subst h₃
    rename_i y' h
    simp [State.IsClosed_iff]
    and_intros
    . apply Memory.assign_closed
      . exact h₂.1
      apply BoxValue.assign_closed at h
      assumption
    . apply Environment.IsClosed_transport st.mem _ st.env
      . exact h₁.mem
      . exact h₁.env
      . apply Memory.assign_monotonic
        apply BoxValue.assign_same_shape at h
        assumption
      . rfl
      . exact h₂.env

private abbrev OnlyVars (ctx : Context) : Prop :=
  ∀ x ∈ ctx, ctx.lookup x = .some true

private theorem evalPattern_context_aux (ctx : Context) (mem : Memory)
                                        (x : RValue) (p : Pattern) (xs : SimpleEnv)
                                        (h : evalPattern mem x p = .some xs)
: xs.context ∪ ctx = ctx.addVars p.vars ∧ OnlyVars xs.context := by
  unfold OnlyVars
  induction p
  using Pattern.rec (motive_2 := fun ps => (ctx : Context) -> (xs : List RValue) -> (env : SimpleEnv) -> evalPatternList mem xs ps = .some env -> env.context ∪ ctx = ctx.addVars (Pattern.listVars ps) ∧ OnlyVars env.context)
  generalizing ctx x xs with
  | wildcard =>
    simp at h
    subst h
    simp
  | const n =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
  | string s =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
  | array ps ih =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> try simp at h
    apply ih
    assumption
  | sexp t ps ih =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> try simp at h
    obtain ⟨ rfl, h ⟩ := h
    apply ih
    assumption
  | named xn p ih =>
    simp [Option.bind] at h
    split at h <;> simp at h
    subst h
    rename_i xs h
    specialize ih (ctx.insert xn true) _ _ h
    and_intros
    . rw [<- ih.1]
      replace ih := ih.2
      apply Finmap.ext_lookup
      intro x'
      by_cases hx' : x' ∈ xs
      . rw [Finmap.lookup_union_left]
        on_goal 2 => simp [hx']
        rw [Finmap.lookup_union_left]
        on_goal 2 => simp [hx']
        by_cases hx : x' = xn
        . subst x'
          specialize ih xn ?_
          . simp [hx']
          rw [ih]
          simp
        . simp [Finmap.lookup_insert_of_ne _ hx]
      by_cases hx : x' = xn
      . subst x'
        rw [Finmap.lookup_union_left]
        on_goal 2 => simp
        rw [Finmap.lookup_union_right]
        on_goal 2 => simp [hx']
        simp
      rw [Finmap.lookup_union_right]
      on_goal 2 => simp [hx, hx']
      rw [Finmap.lookup_union_right]
      on_goal 2 => simp [hx']
      rw [Finmap.lookup_insert_of_ne _ hx]
    . replace ih := ih.2
      intro x' hx'
      simp at hx'
      replace hx' : x' = xn ∨ x' ≠ xn ∧ x' ∈ xs := by tauto
      obtain rfl | ⟨ hx, hx' ⟩ := hx'
      . simp
      simp only [Finmap.lookup_map, Finmap.lookup_insert_of_ne _ hx]
      convert ih x' _
      . simp
      . simp [hx']
  | boxTag =>
    simp at h
    split at h <;> simp at h
    subst h
    simp
  | valTag =>
    simp at h
    split at h <;> simp at h
    subst h
    simp
  | strTag =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    subst h
    simp
  | sexpTag =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    subst h
    simp
  | arrayTag =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    subst h
    simp
  | funTag =>
    simp [Option.bind] at h
    split at h <;> simp at h
    split at h <;> simp at h
    subst h
    simp
  | nil ctx xs env h =>
    unfold OnlyVars
    cases xs with
    | nil =>
      simp at h
      subst h
      simp
    | cons => simp at h
  | cons p ps ih₁ ih₂ ctx xs env h =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp [Option.bind] at h
      split at h <;> simp at h
      rename_i env₁ h₁
      split at h <;> simp at h
      subst h
      rename_i env₂ h₂
      specialize ih₁ ctx _ _ h₁
      specialize ih₂ (ctx.addVars p.vars) _ _ h₂
      simp
      and_intros
      . simp [Finmap.union_assoc, ih₁.1, ih₂.1]
        apply Context.addVars_perm
        apply List.perm_append_comm
      intro x'
      replace ih₁ := ih₁.2 x'
      replace ih₂ := ih₂.2 x'
      simp [-Option.map_eq_some_iff] at ih₁ ih₂ ⊢
      intro hx'
      replace hx' : x' ∈ env₂ ∨ x' ∉ env₂ ∧ x' ∈ env₁ := by tauto
      obtain hx' | ⟨ hx', hx'' ⟩ := hx'
      . left
        apply ih₂
        assumption
      . right
        simp [hx', -Option.map_eq_some_iff]
        apply ih₁
        assumption

theorem evalPattern_context (ctx : Context) (mem : Memory)
                            (x : RValue) (p : Pattern) (xs : SimpleEnv)
                            (h : evalPattern mem x p = .some xs)
: xs.context ∪ ctx = ctx.addVars p.vars := by
  apply evalPattern_context_aux at h
  exact h.1

theorem chooseCase_env_closed (ctx : Context) (bs : List (Pattern × Expr))
                              (mem : Memory) (x : Value) (xs : SimpleEnv) (e : Expr)
                              (h : chooseCase mem x bs = .ok (xs, e))
: xs.IsClosed ctx := by
  unfold chooseCase at h
  simp [Bind.bind, Except.bind] at h
  split at h <;> simp at h
  rename_i x hx
  simp at hx
  subst hx
  fun_induction chooseCaseR with
  | case1 => simp at h
  | case2 p e bs xs h =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    apply evalPattern_context ∅ at h
    simp at h
    intro x' y' hy'
    suffices y'.isVar by
      cases y' <;> simp at this
      simp
    apply_fun Finmap.lookup x' at h
    simp [hy'] at h
    symm at h
    simp at h
    simp [h]
  | case3 p e bs h' ih =>
    simp [h] at ih
    assumption

theorem chooseCase_expr_closed (ctx : Context) (bs : List (Pattern × Expr))
                               (mem : Memory) (x : Value) (xs : SimpleEnv) (e : Expr)
                               (h₁ : ∀ b ∈ bs, b.2.IsClosed (ctx.addVars b.1.vars))
                               (h₂ : chooseCase mem x bs = .ok (xs, e))
: e.IsClosed (xs.context ∪ ctx) := by
  unfold chooseCase at h₂
  simp [Bind.bind, Except.bind] at h₂
  split at h₂ <;> simp at h₂
  rename_i x hx
  simp at hx
  subst hx
  fun_induction chooseCaseR with
  | case1 => simp at h₂
  | case2 p e bs xs h =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    specialize h₁ (p, e) ?_
    . simp
    simp at h₁
    apply evalPattern_context ctx at h
    simp [h, h₁]
  | case3 p e bs h ih =>
    apply ih _ h₂
    intro b hb
    apply h₁
    simp [hb]

theorem prepareDefList_env_closed (ctx : Context) (ds : List Definition)
                                  (xs : SimpleEnv) (e : Expr)
                                  (h₁ : ∀ d ∈ ds, d.IsClosed ctx)
                                  (h₂ : prepareDefList ds = (xs, e))
: xs.IsClosed ctx := by
  fun_induction prepareDefList generalizing xs e with
  | case1 =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    simp [SimpleEnv.IsClosed]
  | case2 x y ds xs e h₂ h₃ ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    specialize ih _ _ ?_ h₂
    . intro d hd
      apply h₁
      simp [hd]
    assumption
  | case3 x y ds xs e h₂ h₃ ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    specialize ih _ _ ?_ h₂
    . intro d hd
      apply h₁
      simp [hd]
    intro x' y' hy'
    by_cases hx' : x' = x
    . subst x'
      simp at hy'
      subst hy'
      simp
    rw [Finmap.lookup_insert_of_ne _ hx'] at hy'
    apply ih
    assumption
  | case4 x params body ds xs e h xs' ih =>
    simp at h₂
    obtain ⟨ rfl, rfl ⟩ := h₂
    subst xs'
    specialize ih _ _ ?_ h
    . intro d hd
      apply h₁
      simp [hd]
    split_ifs with hx
    . assumption
    intro x' y' hy'
    by_cases hx' : x' = x
    . subst x'
      simp at hy'
      subst hy'
      specialize h₁ (.fn x params body) ?_
      . simp
      simp at h₁
      simp [h₁]
    rw [Finmap.lookup_insert_of_ne _ hx'] at hy'
    apply ih
    assumption

theorem prepareDefList_expr_closed (ctx : Context) (ds : List Definition)
                                   (xs : SimpleEnv) (e : Expr)
                                   (h₁ : ∀ d ∈ ds, d.IsClosed ctx)
                                   (h₂ : ∀ x f, xs.context.lookup x = .some f -> ctx.lookup x = .some f)
                                   (h₃ : prepareDefList ds = (xs, e))
: e.IsClosed ctx := by
  fun_induction prepareDefList generalizing xs e with
  | case1 =>
    simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    simp
  | case2 x y ds xs e h₃ h₄ ih =>
    simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    specialize ih _ _ ?_ ?_ h₃
    . intro d hd
      apply h₁
      simp [hd]
    . exact h₂
    specialize h₁ (.var x y) ?_
    . simp
    simp at h₁
    simp [ih, h₁]
  | case3 x y ds xs e h₃ h₄ ih =>
    simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    specialize ih _ _ ?_ ?_ h₃
    . intro d hd
      apply h₁
      simp [hd]
    . intro x' y' hy'
      simp at hy'
      apply h₂
      suffices x' ≠ x by
        simp [Finmap.lookup_insert_of_ne _ this]
        exact hy'
      intro rfl
      rw [Finmap.mem_iff] at h₄
      apply h₄
      obtain ⟨ _, hy', - ⟩ := hy'
      simp [hy']
    specialize h₁ (.var x y) ?_
    . simp
    simp [ih, h₁]
    apply h₂
    simp
  | case4 x params body ds xs e h xs' ih =>
    simp at h₃
    obtain ⟨ rfl, rfl ⟩ := h₃
    subst xs'
    apply ih
    . intro d hd
      apply h₁
      simp [hd]
    . intro x' y' hy'
      apply h₂
      split_ifs with hx
      . assumption
      simp at hy'
      suffices x' ≠ x by
        simp [Finmap.lookup_insert_of_ne _ this]
        exact hy'
      intro rfl
      rw [Finmap.mem_iff] at hx
      apply hx
      obtain ⟨ _, hy', - ⟩ := hy'
      simp [hy']
    . assumption

theorem prepareDefList_expr_closed' (ctx : Context) (ds : List Definition)
                                    (xs : SimpleEnv) (e : Expr)
                                    (h₁ : ∀ d ∈ ds, d.IsClosed (xs.context ∪ ctx))
                                    (h₂ : prepareDefList ds = (xs, e))
: e.IsClosed (xs.context ∪ ctx) := by
  apply prepareDefList_expr_closed at h₂
  . assumption
  . assumption
  intro x f hf
  simp [hf]

theorem prepareDefList_env_context (ctx : Context) (ds : List Definition)
                                   (xs : SimpleEnv) (e : Expr)
                                   (h : prepareDefList ds = (xs, e))
: ctx.addDefs ds = xs.context ∪ ctx := by
  fun_induction prepareDefList generalizing ctx xs e with
  | case1 =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
  | case2 x y ds xs e h₁ h₂ ih =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp [h₁] at ih
    simp [ih]
    apply Finmap.ext_lookup
    intro x'
    by_cases hx' : x' ∈ xs
    . repeat rw [Finmap.lookup_union_left] <;> simp [hx']
    rw [Finmap.lookup_union_right]
    on_goal 2 => simp [hx']
    rw [Finmap.lookup_union_right]
    on_goal 2 => simp [hx']
    rw [Finmap.lookup_insert_of_ne]
    intro rfl
    simp [h₂] at hx'
  | case3 x y ds xs e h₁ h₂ ih =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp [h₁] at ih
    simp [ih]
    apply Finmap.ext_lookup
    intro x'
    by_cases hx' : x' = x
    . subst x'
      simp [h₂]
    replace h₂ := hx'
    clear hx'
    by_cases hx' : x' ∈ xs
    . rw [Finmap.lookup_union_left]
      on_goal 2 => simp [hx']
      rw [Finmap.lookup_union_left]
      on_goal 2 => simp [hx']
      simp [Finmap.lookup_insert_of_ne _ h₂]
    rw [Finmap.lookup_union_right]
    on_goal 2 => simp [hx']
    rw [Finmap.lookup_union_right]
    on_goal 2 => simp [hx', h₂]
    rw [Finmap.lookup_insert_of_ne _ h₂]
  | case4 x params body ds xs e h' xs' ih =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    subst xs'
    simp [h'] at ih
    simp [ih]
    apply Finmap.ext_lookup
    intro x'
    split_ifs with hx
    . by_cases hx' : x' ∈ xs
      . repeat rw [Finmap.lookup_union_left] <;> simp [hx']
      rw [Finmap.lookup_union_right]
      on_goal 2 => simp [hx']
      rw [Finmap.lookup_union_right]
      on_goal 2 => simp [hx']
      rw [Finmap.lookup_insert_of_ne]
      intro rfl
      simp [hx] at hx'
    . by_cases hx' : x' = x
      . subst x'
        simp [hx]
      replace hx := hx'
      clear hx'
      by_cases hx' : x' ∈ xs
      . rw [Finmap.lookup_union_left]
        on_goal 2 => simp [hx']
        rw [Finmap.lookup_union_left]
        on_goal 2 => simp [hx']
        simp [Finmap.lookup_insert_of_ne _ hx]
      rw [Finmap.lookup_union_right]
      on_goal 2 => simp [hx']
      rw [Finmap.lookup_union_right]
      on_goal 2 => simp [hx', hx]
      rw [Finmap.lookup_insert_of_ne _ hx]

theorem Eval_state_closed (st st' : State) (e : Expr) (v : Value)
                          (h₁ : st.WF) (h₂ : st.IsClosed)
                          (h₃ : e.IsClosed st.context)
                          (h₄ : Eval st e (.ok v st'))
: st'.IsClosed := by
  generalize hr : Result.ok v st' = r at *
  symm at hr
  induction h₄
  using Eval.rec (motive_2 := fun st es r _ => st.WF -> st.IsClosed -> (∀ e ∈ es, e.IsClosed st.context)
                                            -> (st' : State) -> (ys : List RValue) -> r = .ok ys st' -> st'.IsClosed)
  generalizing v st'
  with
  | skip =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    assumption
  | varOk st st' x y h =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply evalVar_state_closed at h <;> assumption
  | varErr => simp at hr
  | refOk =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    assumption
  | refErr => simp at hr
  | int =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    assumption
  | str st st' s box h =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply State.allocWith_closed at h <;> assumption
  | arrOk st₁ st₂ st₃ xs ys box h₄ h₅ ih =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp [h₁, h₂] at ih
    apply State.allocWith_closed at h₅
    on_goal 4 => simp
    . assumption
    . apply EvalList_result_wf at h₄
      . exact h₄.2
      . assumption
    apply ih
    simp at h₃
    assumption
  | arrErr => simp at hr
  | sexpOk st₁ st₂ st₃ t xs ys box h₄ h₅ ih =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp [h₁, h₂] at ih
    apply State.allocWith_closed at h₅
    on_goal 4 => simp
    . assumption
    . apply EvalList_result_wf at h₄
      . exact h₄.2
      . assumption
    apply ih
    simp at h₃
    assumption
  | sexpErr => simp at hr
  | lambdaOk st st' xs x box env h₄ h₅ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply State.allocWith_closed at h₅ <;> try assumption
    simp
    rw [Environment.close_context _ _ _ h₄]
    simp [State.IsClosed_iff] at h₂
    apply Environment.close_closed at h₄ <;> simp [*]
  | lambdaErr => simp at hr
  | binopOk st₁ st₂ st₃ op x₁ x₂ y₁ y₂ z h₄ h₅ h₆ ih₁ ih₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply ih₂
    on_goal 4 => rfl
    on_goal 3 =>
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      exact h₄.2
    apply ih₁
    . assumption
    . assumption
    . exact h₃.1
    . rfl
  | binopErr => simp at hr
  | binopErrL => simp at hr
  | binopErrR => simp at hr
  | elemOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₄ h₅ h₆ ih₁ ih₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply ih₂
    on_goal 4 => rfl
    on_goal 3 =>
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      exact h₄.2
    apply ih₁
    . assumption
    . assumption
    . exact h₃.1
    . rfl
  | elemErr => simp at hr
  | elemErrL => simp at hr
  | elemErrR => simp at hr
  | elemRefOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₄ h₅ h₆ ih₁ ih₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply ih₂
    on_goal 4 => rfl
    on_goal 3 =>
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      exact h₄.2
    apply ih₁
    . assumption
    . assumption
    . exact h₃.1
    . rfl
  | elemRefErr => simp at hr
  | elemRefErrL => simp at hr
  | elemRefErrR => simp at hr
  | callOk st₁ st₂ st₃ st₄ st₅ x xs y ys z z' h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    unfold commitCall at hr
    cases z' <;> simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    rename_i z'
    simp at h₃
    have hwf₁ := Eval_result_wf _ _ _ ?_ h₄
    on_goal 2 => assumption
    simp at hwf₁
    have hwf₂ := EvalList_result_wf _ _ _ ?_ h₅
    on_goal 2 => simp [hwf₁]
    simp at hwf₂
    -- have hwf₃ := prepareCall_state_wf _ _ _ _ _ ?_ ?_ h₆
    -- on_goal 2 => exact hwf₂.2.mem
    -- on_goal 2 => exact hwf₂.1
    specialize ih₁ _ _ ?_ ?_ ?_ rfl
    . assumption
    . assumption
    . exact h₃.1
    specialize ih₂ _ _ ?_ ?_ ?_ rfl
    . simp [hwf₁]
    . assumption
    . rw [<- State.context_transport]
      . exact h₃.2
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    specialize ih₃ _ _ ?_ ?_ ?_ rfl
    . apply prepareCall_state_wf at h₆
      . assumption
      . exact hwf₂.2.mem
      . exact hwf₂.1
    . simp [State.IsClosed_iff, <- prepareCall_memory (h := h₆), ih₂.mem]
      apply prepareCall_env_closed at h₆
      assumption
    . apply prepareCall_expr_closed at h₆
      . assumption
      . exact ih₂.mem
    simp [State.IsClosed_iff, ih₃.mem]
    apply Environment.IsClosed_transport st₃.mem (h₄ := by rfl)
    . exact hwf₂.2.mem
    . exact hwf₂.2.env
    . apply prepareCall_memory at h₆
      rw [h₆]
      apply Eval_state_monotonic at h₇
      exact h₇.mem
    exact ih₂.env
  | callErr₁ => simp at hr
  | callErr₂ => simp at hr
  | callErr₃ => simp at hr
  | callErr₄ => simp at hr
  | assignOk st₁ st₂ st₃ st₄ x₁ x₂ y₁ y₂ z h₄ h₅ h₆ ih₁ ih₂ =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    simp at h₃
    specialize ih₁ _ _ h₁ h₂ h₃.1 rfl
    have hwf : st₂.WF := by
      apply Eval_result_wf at h₄
      . simp at h₄
        simp [h₄]
      . assumption
    specialize ih₂ _ _ hwf ih₁ ?_ rfl
    . rw [<- State.context_transport]
      . exact h₃.2
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    apply evalAssign_state_closed at h₆ <;> try assumption
    apply Eval_result_wf at h₅
    . exact h₅.2
    . assumption
  | assignErr => simp at hr
  | assignErrL => simp at hr
  | assignErrR => simp at hr
  | seqOk st₁ st₂ x₁ x₂ y₁ res h₄ h₅ ih₁ ih₂ =>
    subst hr
    apply ih₂
    on_goal 4 => rfl
    on_goal 3 =>
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      exact h₄.2
    apply ih₁
    . assumption
    . assumption
    . exact h₃.1
    . rfl
  | seqErr => simp at hr
  | iteThen st st' x₁ x₂ x₃ y₁ res h₄ h₅ h₆ ih₁ ih₂ =>
    subst hr
    apply ih₂
    on_goal 4 => rfl
    on_goal 3 =>
      obtain ⟨ -, h₃, - ⟩ := h₃
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      exact h₄.2
    apply ih₁
    . assumption
    . assumption
    . exact h₃.1
    . rfl
  | iteElse st st' x₁ x₂ x₃ y₁ res h₄ h₅ h₆ ih₁ ih₂ =>
    subst hr
    apply ih₂
    on_goal 4 => rfl
    on_goal 3 =>
      obtain ⟨ -, -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    . apply Eval_result_wf at h₄
      on_goal 2 => assumption
      exact h₄.2
    apply ih₁
    . assumption
    . assumption
    . exact h₃.1
    . rfl
  | iteErr₁ => simp at hr
  | iteErr₂ => simp at hr
  | loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res h₄ h₅ h₆ h₇ ih₁ ih₂ ih₃ =>
    subst hr
    have hwf₂ : st₂.WF := by
      apply Eval_result_wf at h₄
      on_goal 2 => assumption
      exact h₄.2
    have hwf₃ : st₃.WF := by
      apply Eval_result_wf at h₆
      on_goal 2 => exact hwf₂
      exact h₆.2
    apply ih₃ _ _ hwf₃
    on_goal 3 => rfl
    on_goal 2 =>
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      apply Eval_state_monotonic at h₆
      grw [h₄, h₆]
    apply ih₂ _ _ hwf₂
    on_goal 3 => rfl
    on_goal 2 =>
      obtain ⟨ -, h₃ ⟩ := h₃
      rw [State.context_transport] at h₃
      . exact h₃
      . assumption
      apply Eval_state_monotonic at h₄
      assumption
    apply ih₁
    . assumption
    . assumption
    . exact h₃.1
    . rfl
  | loopStop st st' x₁ x₂ y₁ h₄ h₅ ih =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply ih
    . assumption
    . assumption
    . exact h₃.1
    . rfl
  | loopErr => simp at hr
  | loopErrL => simp at hr
  | loopErrR => simp at hr
  | caseOk st st' x₁ bs y₁ xs x₂ res h₄ h₅ h₆ ih₁ ih₂ =>
    apply Result.popEnv_state at hr
    obtain ⟨ str, rfl, hr ⟩ := hr
    unfold State.popEnv at hr
    simp [Option.bind] at hr
    split at hr <;> simp at hr
    subst st'
    rename_i env h
    unfold Environment.pop at h
    split at h <;> simp at h
    subst h
    rename_i xs' env h
    simp at h₃
    specialize ih₁ _ _ ?_ ?_ ?_ rfl
    . assumption
    . assumption
    . exact h₃.1
    have hwf := Eval_result_wf _ _ _ h₁ h₄
    simp at hwf
    specialize ih₂ _ _ ?_ ?_ ?_ rfl
    . simp [State.WF_iff, hwf.2.mem, hwf.2.env]
      apply chooseCase_env_wf at h₅
      apply h₅ <;> simp [hwf.2.mem, hwf]
    . simp [State.IsClosed_iff, ih₁.mem, ih₁.env]
      apply chooseCase_env_closed at h₅
      exact h₅
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
    . simp [State.IsClosed_iff, h] at ih₂
      simp [State.IsClosed_iff, ih₂]
  | caseErr₁ => simp at hr
  | caseErr₂ => simp at hr
  | scope st x₁ xs x₂ res h₄ h₅ ih =>
    apply Result.popEnv_state at hr
    obtain ⟨ str, rfl, hr ⟩ := hr
    unfold State.popEnv at hr
    simp [Option.bind] at hr
    split at hr <;> simp at hr
    subst st'
    rename_i env h
    unfold Environment.pop at h
    split at h <;> simp at h
    subst h
    rename_i xs' env h
    obtain ⟨ ds, x₁ ⟩ := x₁
    simp at h₃ h₄ h₅
    rw [prepareDefList_env_context _ _ _ _ h₄] at h₃
    specialize ih _ _ ?_ ?_ ?_ rfl
    . simp [State.WF_iff, h₁.mem, h₁.env]
      apply prepareDefList_env_wf at h₄
      assumption
    . simp [State.IsClosed_iff, h₂.mem, h₂.env]
      apply prepareDefList_env_closed at h₄
      . assumption
      . exact h₃.2
    . simp [h₃.1]
      apply prepareDefList_expr_closed' at h₄
      . exact h₄
      . exact h₃.2
    . simp [State.IsClosed_iff, h] at ih
      simp [State.IsClosed_iff, ih]
  | nil st h₁ h₂ h₃ st' ys hr =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    assumption
  | cons st₁ st₂ st₃ x xs y ys h₁ h₂ ih₁ ih₂ h₃ h₄ h₅ st' ys hr =>
    simp at hr
    obtain ⟨ rfl, rfl ⟩ := hr
    apply ih₂
    on_goal 4 => rfl
    on_goal 3 =>
      intro e he
      rw [State.context_transport] at h₅
      . apply h₅
        simp [he]
      . assumption
      apply Eval_state_monotonic at h₁
      assumption
    . apply Eval_result_wf at h₁
      on_goal 2 => assumption
      exact h₁.2
    apply ih₁
    . assumption
    . assumption
    . apply h₅
      simp
    . rfl
  | err st st' x xs y h₁ ih h₃ h₄ h₅ st' ys hr => simp at hr
  | errL st x xs e h₁ ih h₂ h₃ h₄ st' ys hr => simp at hr
  | errR st st' x xs y e h₁ h₂ ih₁ ih₂ h₃ h₄ h₅ st' ys hr => simp at hr

theorem EvalList_state_closed (st st' : State)
                              (es : List Expr) (xs : List RValue)
                              (h₁ : st.WF) (h₂ : st.IsClosed)
                              (h₃ : ∀ e ∈ es, e.IsClosed st.context)
                              (h₄ : EvalList st es (.ok xs st'))
: st'.IsClosed := by
  induction es generalizing st st' xs with
  | nil =>
    cases h₄ with
    | nil => assumption
  | cons e es ih =>
    cases h₄ with
    | cons _ st₂ _ _ _ x xs h₄ h₅ =>
      have hwf : st₂.WF := by
        apply Eval_result_wf at h₄
        . exact h₄.2
        . assumption
      apply ih at h₅
      . assumption
      . assumption
      on_goal 2 =>
        rw [State.context_transport _ st₂] at h₃
        . intro e he
          apply h₃
          simp [he]
        . assumption
        apply Eval_state_monotonic at h₄
        assumption
      apply Eval_state_closed at h₄
      . assumption
      . assumption
      . assumption
      . apply h₃
        simp
