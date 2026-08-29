import Lama.Semantics.Eval


namespace Except

variable {ε : Type u} {α β : Type v} {r : α -> α -> Prop}

@[simp]
theorem map_toOption (f : α -> β) (x : Except ε α)
: (f <$> x).toOption = f <$> x.toOption := by
  cases x <;> simp [Except.toOption]

def SameShape (r : α -> α -> Prop)
: Except ε α -> Except ε α -> Prop
| .error x, .error y => x = y
| .ok x, .ok y => r x y
| _, _ => False

@[simp]
theorem SameShape_error (e : ε) (y : Except ε α)
: SameShape r (.error e) y <-> y = .error e := by
  cases y <;> simp [SameShape]
  constructor <;> intro rfl <;> rfl

@[simp]
theorem SameShape_ok (x : α) (y : Except ε α)
: SameShape r (.ok x) y <-> ∃ y', y = .ok y' ∧ r x y' := by
  cases y <;> simp [SameShape]

@[refl, simp]
theorem SameShape_refl [h : Std.Refl r] (x : Except ε α)
: SameShape r x x := by
  cases x <;> simp
  apply h.refl

instance [Std.Refl r] : @Std.Refl (Except ε α) (SameShape r) := ⟨ SameShape_refl ⟩

@[simp] -- `symm` causes unbounded metavariables
theorem SameShape_symm [h₁ : Std.Symm r]
                       (x y : Except ε α)
                       (h₂ : SameShape r x y)
: SameShape r y x := by
  cases x <;> simp at *
  . subst h₂
    simp
  obtain ⟨ y, rfl, h₂ ⟩ := h₂
  apply h₁.symm; assumption

instance [Std.Symm r] : @Std.Symm (Except ε α) (SameShape r) := ⟨ SameShape_symm ⟩

@[trans]
theorem SameShape_trans [h₁ : IsTrans _ r] (x y z : Except ε α)
                        (h₂ : SameShape r x y) (h₃ : SameShape r y z)
: SameShape r x z := by
  cases x <;> simp at h₂
  . subst h₂
    simp at h₃
    subst h₃
    simp
  obtain ⟨ y, rfl, h₂ ⟩ := h₂
  simp at h₃
  obtain ⟨ z, rfl, h₃ ⟩ := h₃
  simp
  trans <;> assumption

instance [IsTrans _ r] : IsTrans (Except ε α) (SameShape r) := ⟨ SameShape_trans ⟩

end Except

namespace Option

variable {α : Type u} {r : α -> α -> Prop}

@[simp]
theorem Rel_none (y : Option α)
: Rel r .none y <-> y = .none := by
  cases y <;> simp

@[simp]
theorem Rel_some (x : α) (y : Option α)
: Rel r (.some x) y <-> ∃ y', y = .some y' ∧ r x y' := by
  cases y <;> simp

@[refl, simp]
theorem Rel_refl [h : Std.Refl r] (x : Option α)
: Rel r x x := by
  cases x <;> simp
  apply h.refl

instance [Std.Refl r] : Std.Refl (Rel r) := ⟨ Rel_refl ⟩

@[simp] -- `symm` causes unbounded metavariables
theorem Rel_symm [h₁ : Std.Symm r]
                 (x y : Option α)
                 (h₂ : Rel r x y)
: Rel r y x := by
  cases x <;> cases y <;> simp at *
  apply h₁.symm; assumption

instance [Std.Symm r] : Std.Symm (Rel r) := ⟨ Rel_symm ⟩

@[trans]
theorem Rel_trans [h₁ : IsTrans _ r] (x y z : Option α)
                  (h₂ : Rel r x y) (h₃ : Rel r y z)
: Rel r x z := by
  cases x <;> simp at h₂
  . subst h₂
    simp at h₃
    subst h₃
    simp
  obtain ⟨ y, rfl, h₂ ⟩ := h₂
  simp at h₃
  obtain ⟨ z, rfl, h₃ ⟩ := h₃
  simp
  trans <;> assumption

instance [IsTrans _ r] : IsTrans _ (Rel r) := ⟨ Rel_trans ⟩

@[simp]
theorem toExcept_same_shape {ε : Type v} (e : ε) (x y : Option α)
: Except.SameShape r (x.toExcept e) (y.toExcept e) <-> Rel r x y := by
  cases x <;> simp

end Option

namespace Lama.Semantics

open Lama.Ast

def EnvValue.SameShape : EnvValue -> EnvValue -> Prop
| var _, var _ => True
| fn xs₁ b₁, fn xs₂ b₂ => xs₁ = xs₂ ∧ b₁ = b₂
| _, _ => False

@[simp]
theorem EnvValue.SameShape_var (x : RValue) (y : EnvValue)
: SameShape (var x) y <-> ∃ y', y = .var y' := by
  cases y <;> simp [SameShape]

@[simp]
theorem EnvValue.SameShape_fn (xs : List Ident) (b : Expr)
                              (y : EnvValue)
: SameShape (fn xs b) y <-> y = .fn xs b := by
  cases y <;> simp [SameShape]
  constructor <;> intro ⟨ rfl, rfl ⟩ <;> simp

@[refl, simp]
theorem EnvValue.SameShape_refl (x : EnvValue) : x.SameShape x := by
  cases x <;> simp

instance : Std.Refl EnvValue.SameShape := ⟨ EnvValue.SameShape_refl ⟩

@[symm, simp]
theorem EnvValue.SameShape_symm (x y : EnvValue)
                                (h : x.SameShape y)
: y.SameShape x := by
  cases x <;> cases y <;> simp at *
  simp [*]

instance : Std.Symm EnvValue.SameShape := ⟨ EnvValue.SameShape_symm ⟩

@[trans]
theorem EnvValue.SameShape_trans (x y z : EnvValue)
                                 (h₁ : x.SameShape y)
                                 (h₂ : y.SameShape z)
: x.SameShape z := by
  cases x <;> cases y
  all_goals simp at *
  all_goals simp [*]

instance : IsTrans _ EnvValue.SameShape := ⟨ EnvValue.SameShape_trans ⟩

def SimpleEnv.SameShape (xs₁ xs₂ : SimpleEnv) : Prop :=
  ∀ x, Option.Rel EnvValue.SameShape (xs₁.lookup x) (xs₂.lookup x)

@[refl, simp]
theorem SimpleEnv.SameShape_refl (xs : SimpleEnv)
: xs.SameShape xs := by
  simp [SameShape]

instance : Std.Refl SimpleEnv.SameShape := ⟨ SimpleEnv.SameShape_refl ⟩

@[symm, simp]
theorem SimpleEnv.SameShape_symm (xs ys : SimpleEnv)
                                 (h : xs.SameShape ys)
: ys.SameShape xs := by
  simp [SameShape] at *
  intro x; simp [h]

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

@[simp]
def ClosedEnv.SameShape
: ClosedEnv -> ClosedEnv -> Prop
| empty, empty => True
| scope xs₁ env₁, scope xs₂ env₂ =>
  xs₁.SameShape xs₂ ∧ env₁.SameShape env₂
| _, _ => False

@[simp]
theorem ClosedEnv.SameShape_empty (y : ClosedEnv)
: SameShape .empty y <-> y = .empty := by
  cases y <;> simp

@[simp]
theorem ClosedEnv.SameShape_scope (xs : SimpleEnv) (env y : ClosedEnv)
: SameShape (.scope xs env) y <-> ∃ xs' env', y = .scope xs' env' ∧ xs.SameShape xs' ∧ env.SameShape env' := by
  cases y <;> simp

@[refl, simp]
theorem ClosedEnv.SameShape_refl (x : ClosedEnv) : x.SameShape x := by
  induction x <;> simp [*]

instance : Std.Refl ClosedEnv.SameShape := ⟨ ClosedEnv.SameShape_refl ⟩

@[symm, simp]
theorem ClosedEnv.SameShape_symm (x y : ClosedEnv)
                                 (h : x.SameShape y)
: y.SameShape x := by
  fun_induction SameShape x y with
  | case1 => simp
  | case2 xs₁ env₁ xs₂ env₂ ih =>
    simp
    and_intros
    on_goal 2 =>
      apply ih
      simp [h]
    intro x
    simp [h.1 _]
  | case3 => simp at h

instance : Std.Symm ClosedEnv.SameShape := ⟨ ClosedEnv.SameShape_symm ⟩

@[trans]
theorem ClosedEnv.SameShape_trans (x y z : ClosedEnv)
                                  (h₁ : x.SameShape y)
                                  (h₂ : y.SameShape z)
: x.SameShape z := by
  fun_induction SameShape x y generalizing z with
  | case1 => assumption
  | case3 => simp at h₁
  | case2 xs₁ env₁ xs₂ env₂ ih =>
    cases z <;> simp at *
    case scope xs₃ env₃ =>
      specialize ih _ h₁.2 h₂.2
      simp [ih]
      intro x
      replace h₁ := h₁.1 x
      replace h₂ := h₂.1 x
      trans <;> assumption

instance : IsTrans _ ClosedEnv.SameShape := ⟨ ClosedEnv.SameShape_trans ⟩

theorem ClosedEnv.assign_same_shape (x : Ident) (y : RValue)
                                    (env env' : ClosedEnv)
                                    (h : env.assign x y = .some env')
: env.SameShape env' := by
  fun_induction assign generalizing env' with
  | case1 => simp at h
  | case2 xs env y' h' =>
    simp at h
    subst h
    simp
    intro x'
    by_cases hx : x' = x
    on_goal 2 => simp [Finmap.lookup_insert_of_ne, hx]
    subst x'
    simp [h', EnvValue.SameShape]
  | case3 => simp at h
  | case4 xs env h' ih =>
    simp [Option.bind] at h
    split at h <;> simp at h
    subst h
    rename_i y' h
    simp
    apply ih _ h

def EnvLookup.SameShape : EnvLookup -> EnvLookup -> Prop
| var _, var _ => True
| fn env₁ xs₁ b₁, fn env₂ xs₂ b₂ => env₁.SameShape env₂ ∧ xs₁ = xs₂ ∧ b₁ = b₂
| _, _ => False

@[simp]
theorem EnvLookup.SameShape_var (x : RValue) (y : EnvLookup)
: SameShape (var x) y <-> ∃ y', y = .var y' := by
  cases y <;> simp [SameShape]

@[simp]
theorem EnvLookup.SameShape_fn (xs : List Ident) (b : Expr)
                               (env : ClosedEnv) (y : EnvLookup)
: SameShape (fn env xs b) y <-> ∃ env', y = .fn env' xs b ∧ env.SameShape env' := by
  cases y <;> simp [SameShape]
  constructor
  . intro ⟨ h, rfl, rfl ⟩
    simp [h]
  . intro ⟨ ⟨ rfl, rfl ⟩, h ⟩
    simp [h]

@[refl, simp]
theorem EnvLookup.SameShape_refl (x : EnvLookup) : x.SameShape x := by
  cases x <;> simp

instance : Std.Refl EnvLookup.SameShape := ⟨ EnvLookup.SameShape_refl ⟩

@[symm, simp]
theorem EnvLookup.SameShape_symm (x y : EnvLookup)
                                 (h : x.SameShape y)
: y.SameShape x := by
  cases x <;> cases y <;> simp at *
  simp [*]

instance : Std.Symm EnvLookup.SameShape := ⟨ EnvLookup.SameShape_symm ⟩

@[trans]
theorem EnvLookup.SameShape_trans (x y z : EnvLookup)
                                  (h₁ : x.SameShape y)
                                  (h₂ : y.SameShape z)
: x.SameShape z := by
  cases x
  all_goals simp at *
  . obtain ⟨ y', rfl ⟩ := h₁
    simp at h₂
    assumption
  obtain ⟨ env₁, rfl, h₁ ⟩ := h₁
  simp at h₂
  obtain ⟨ env₂, rfl, h₂ ⟩ := h₂
  simp
  trans <;> assumption

instance : IsTrans _ EnvValue.SameShape := ⟨ EnvValue.SameShape_trans ⟩

theorem EnvValue.toLookup_same_shape (x y : EnvValue) (env env' : ClosedEnv)
                                     (h₁ : x.SameShape y) (h₂ : env.SameShape env')
: (x.toLookup env).SameShape (y.toLookup env') := by
  cases x <;> simp at *
  . obtain ⟨ y, rfl ⟩ := h₁
    simp
  subst h₁
  simp [h₂]

theorem ClosedEnv.lookup_same_shape (x : Ident) (env env' : ClosedEnv)
                                    (h : env.SameShape env')
: Option.Rel EnvLookup.SameShape (env x) (env' x) := by
  simp
  fun_induction SameShape with
  | case1 => simp
  | case2 xs₁ env₁ xs₂ env₂ ih =>
    simp
    have := h.1 x
    generalize xs₁.lookup x = y₁ at *
    split <;> simp at this ⊢
    on_goal 2 =>
      simp [this]
      apply ih
      exact h.2
    rename_i y₁
    obtain ⟨ y₂, h₁, h₂ ⟩ := this
    simp [h₁]
    apply EnvValue.toLookup_same_shape
    . assumption
    . simp [h]
  | case3 => simp at h

def BoxValue.SameShape : BoxValue -> BoxValue -> Prop
| undefined, undefined => True
| str xs₁, str xs₂ => xs₁.size = xs₂.size
| arr xs₁, arr xs₂ => xs₁.length = xs₂.length
| sexp t₁ xs₁, sexp t₂ xs₂ => t₁ = t₂ ∧ xs₁.length = xs₂.length
| closure env₁ xs₁ b₁, closure env₂ xs₂ b₂ =>
  env₁.SameShape env₂ ∧ xs₁ = xs₂ ∧ b₁ = b₂
| _, _ => False

@[simp]
theorem BoxValue.SameShape_undefined (y : BoxValue)
: SameShape undefined y <-> y = undefined := by
  cases y <;> simp [SameShape]

@[simp]
theorem BoxValue.SameShape_str (xs : ByteArray) (y : BoxValue)
: SameShape (str xs) y <-> ∃ ys, y = .str ys ∧ xs.size = ys.size := by
  cases y <;> simp [SameShape]

@[simp]
theorem BoxValue.SameShape_arr (xs : List RValue) (y : BoxValue)
: SameShape (arr xs) y <-> ∃ ys, y = .arr ys ∧ xs.length = ys.length := by
  cases y <;> simp [SameShape]

@[simp]
theorem BoxValue.SameShape_sexp (t : Tag) (xs : List RValue) (y : BoxValue)
: SameShape (sexp t xs) y <-> ∃ ys, y = .sexp t ys ∧ xs.length = ys.length := by
  cases y <;> simp [SameShape]; intro
  constructor <;> intro h <;> symm <;> assumption

@[simp]
theorem BoxValue.SameShape_closure (env : ClosedEnv) (xs : List Ident)
                                   (b : Expr) (y : BoxValue)
: SameShape (closure env xs b) y <-> ∃ env', y = .closure env' xs b ∧ env.SameShape env' := by
  cases y <;> simp [SameShape]
  constructor <;> intro h
  . obtain ⟨ h, rfl, rfl ⟩ := h
    simp [h]
  . obtain ⟨ ⟨ rfl, rfl ⟩, h ⟩ := h
    simp [h]

@[refl, simp]
theorem BoxValue.SameShape_refl (x : BoxValue) : x.SameShape x := by
  cases x <;> simp

instance : Std.Refl BoxValue.SameShape := ⟨ BoxValue.SameShape_refl ⟩

@[symm, simp]
theorem BoxValue.SameShape_symm (x y : BoxValue)
                                (h : x.SameShape y)
: y.SameShape x := by
  cases x <;> cases y <;> simp at *
  . symm; assumption
  . symm; assumption
  . obtain ⟨ rfl, h ⟩ := h
    simp [h]
  . obtain ⟨ ⟨ rfl, rfl ⟩, h ⟩ := h
    simp; symm; assumption

instance : Std.Symm BoxValue.SameShape := ⟨ BoxValue.SameShape_symm ⟩

@[trans]
theorem BoxValue.SameShape_trans (x y z : BoxValue)
                                 (h₁ : x.SameShape y)
                                 (h₂ : y.SameShape z)
: x.SameShape z := by
  cases x <;> cases y
  all_goals simp at *
  all_goals try simp [*]
  . obtain ⟨ zs, rfl, h₂ ⟩ := h₂
    simp [h₁, h₂]
  . obtain ⟨ zs, rfl, h₂ ⟩ := h₂
    obtain ⟨ ⟨ rfl, rfl ⟩, h₁ ⟩ := h₁
    simp; trans <;> assumption

instance : IsTrans _ BoxValue.SameShape := ⟨ BoxValue.SameShape_trans ⟩

theorem BoxValue.assign_same_shape (x x' : BoxValue)
                                   (i : ℕ) (y : RValue)
                                   (h : x.assign i y = .ok x')
: x.SameShape x' := by
  fun_cases assign with
  | case1 => simp at h
  | case2 xs =>
    simp [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h <;> try simp at h
    rename_i y' hy'
    simp at hy'
    subst hy'
    split at h <;> try simp at h
    rename_i y hy
    simp at hy
    replace hy : y = y' := by
      unfold Int.toNat? at hy
      split at hy <;> simp at hy
      subst hy
      simp
    subst hy
    split at h <;> try simp at h
    rename_i xs hxs
    simp at hxs
    subst h
    obtain ⟨ h, rfl ⟩ := hxs
    simp; symm
    convert ByteArray.size_set _ ⟨ i, h ⟩ _
  | case3 xs =>
    simp [Functor.map, Except.map] at h
    split at h <;> try simp at h
    rename_i xs hxs
    simp at hxs
    subst h
    obtain ⟨ h, rfl ⟩ := hxs
    simp
  | case4 t xs =>
    simp [Functor.map, Except.map] at h
    split at h <;> try simp at h
    rename_i xs hxs
    simp at hxs
    subst h
    obtain ⟨ h, rfl ⟩ := hxs
    simp
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
  | case2 box env params body h' =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    rename_i env' h
    simp at h
    apply Memory.assign_monotonic
    simp [h', BoxValue.SameShape]
    apply ClosedEnv.assign_same_shape at h
    assumption
  | case3 => simp at h
  | case4 xs env y h' =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
  | case5 => simp at h
  | case6 xt env h ih =>
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

@[simp]
theorem Environment.SameShape_empty (y : Environment)
: SameShape .empty y <-> y = .empty := by
  cases y <;> simp

@[simp]
theorem Environment.SameShape_closure (box : Box) (y : Environment)
: SameShape (.closure box) y <-> y = .closure box := by
  cases y <;> simp
  constructor <;> intro <;> symm <;> assumption

@[simp]
theorem Environment.SameShape_scope (xs : SimpleEnv) (env y : Environment)
: SameShape (.scope xs env) y <-> ∃ xs' env', y = .scope xs' env' ∧ xs.SameShape xs' ∧ env.SameShape env' := by
  cases y <;> simp

@[refl, simp]
theorem Environment.SameShape_refl (x : Environment) : x.SameShape x := by
  induction x <;> simp [*]

instance : Std.Refl Environment.SameShape := ⟨ Environment.SameShape_refl ⟩

@[symm, simp]
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
    simp [h.1 _]

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

theorem Environment.close_same_shape (mem : Memory)
                                     (env env' : Environment)
                                     (h : env.SameShape env')
: Option.Rel ClosedEnv.SameShape (env.close mem) (env'.close mem) := by
  fun_induction SameShape with
  | case1 => simp
  | case2 =>
    subst h
    simp
  | case3 xs₁ env₁ xs₂ env₂ ih =>
    simp [h] at ih
    simp [Option.bind]
    generalize h₁ : env₁.close mem = res₁ at *
    generalize h₂ : env₂.close mem = res₂ at *
    split <;> split <;> simp at *
    simp [h, ih]
  | case4 => simp at h

theorem Environment.lookup_same_shape (x : Ident) (mem : Memory)
                                      (env env' : Environment)
                                      (h : env.SameShape env')
: Except.SameShape EnvLookup.SameShape (env x mem) (env' x mem) := by
  simp
  fun_induction SameShape with
  | case1 => simp
  | case2 box =>
    subst h
    simp
  | case3 xs₁ env₁ xs₂ env₂ ih =>
    simp
    have := h.1 x
    generalize xs₁.lookup x = y₁ at *
    split <;> simp at this ⊢
    on_goal 2 =>
      simp [this]
      apply ih
      exact h.2
    rename_i y₁
    obtain ⟨ y₂, h₁, h₂ ⟩ := this
    simp [h₁, Option.bind]
    have := close_same_shape mem _ _ h.2
    generalize h₃ : env₁.close mem = env₁' at *
    generalize h₄ : env₂.close mem = env₂' at *
    split <;> split <;> simp at *
    apply EnvValue.toLookup_same_shape <;> simp [*]
  | case4 => simp at h

theorem Environment.assign_same_shape (x : Ident) (y : RValue)
                                      (mem mem' : Memory) (env env' : Environment)
                                      (h : env.assign x y mem = .ok (env', mem'))
: env.SameShape env' := by
  fun_induction assign generalizing env' mem' with
  | case1 => simp at h
  | case2 box env params body h' =>
    simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
  | case3 => simp at h
  | case4 xs env y' h =>
    simp at h
    obtain ⟨ rfl, rfl ⟩ := h
    simp
    intro x'
    by_cases hx : x' = x
    on_goal 2 => simp [Finmap.lookup_insert_of_ne, hx]
    subst x'
    simp [h, EnvValue.SameShape]
  | case5 => simp at h
  | case6 xs env h ih =>
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
