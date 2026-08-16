import Mathlib

import Lama.Ast


@[reducible, simp]
def Option.toExcept {α : Type u} {ε : Type v} (e : ε)
: Option α -> Except ε α
| .none => .error e
| .some x => .ok x

@[reducible]
def List.set? {α : Type u} (i : ℕ) (x : α) (xs : List α) : Option (List α) :=
  if i < xs.length
  then .some $ xs.set i x
  else .none

@[reducible]
def ByteArray.set? (i : ℕ) (x : UInt8) (xs : ByteArray) : Option ByteArray :=
  if _ : i < xs.size
  then .some $ xs.set i x
  else .none

namespace Lama.Semantics

open Ast

-- Memory location
structure Box where
  cell : ℕ
deriving Repr, DecidableEq, Inhabited, Hashable

inductive Error where
| metatheory
| name
| lvalue
| type
| runtime
deriving Repr, DecidableEq, Inhabited, Hashable

-- Pure value
inductive RValue where
| int (n : Int)
| box (b : Box)
deriving Repr, DecidableEq, Inhabited, Hashable

@[reducible, simp]
def RValue.toInt? : RValue -> Option Int
| .int n => .some n
| .box _ => .none

@[reducible]
def RValue.toNat? (x : RValue) : Except Error ℕ := do
  let x <- x.toInt?.toExcept .type
  x.toNat?.toExcept .runtime

@[reducible]
def RValue.toBool? (x : RValue) : Option Bool := do
  let x <- x.toInt?
  return x ≠ 0

@[reducible, simp]
def RValue.toBox? : RValue -> Option Box
| .int _ => .none
| .box b => .some b

-- Value in environment
inductive EnvValue where
| var (x : RValue)
| fn (params : List Ident) (body : Expr)

-- Simple (w/o scoping) environment
abbrev SimpleEnv : Type :=
  Finmap fun (_ : Ident) => EnvValue

-- Value in memory
inductive BoxValue where
| str (xs : ByteArray)
| arr (xs : List RValue)
| sexp (t : Tag) (xs : List RValue)
| closure (env : SimpleEnv) (params : List Ident) (body : Expr)

@[reducible, simp]
def BoxValue.assign (i : ℕ) (x : RValue)
: BoxValue -> Except Error BoxValue
| str xs => do
  let x <- x.toNat?
  let xs <- (xs.set? i x.toUInt8).toExcept .runtime
  return str xs
| arr xs => do
  let xs <- (xs.set? i x).toExcept .runtime
  return arr xs
| sexp t xs => do
  let xs <- (xs.set? i x).toExcept .runtime
  return sexp t xs
| closure _ _ _ => .error .type

-- Memory
structure Memory where
  mem : Box -> BoxValue
  bound : ℕ

@[reducible]
instance : CoeFun Memory (fun _ => Box -> BoxValue) where
  coe mem box := mem.mem box

@[reducible]
def Memory.alloc (mem : Memory) : Box × Memory :=
  ⟨ .mk mem.bound, { mem with bound := mem.bound + 1 } ⟩

@[reducible]
def Memory.assign (box : Box) (value : BoxValue) (mem : Memory) : Memory :=
  let mem' box' := if box = box' then value else mem box'
  ⟨ mem', mem.bound ⟩

@[reducible]
def Memory.allocWith (x : BoxValue) (mem : Memory) : Box × Memory :=
  let (box, mem) := mem.alloc
  (box, mem.assign box x)

-- Effective environment
inductive Environment where
| empty
| closure (b : Box)
| scope (xs : SimpleEnv) (parent : Environment)

-- Environment lookup result
inductive EnvLookup where
| var (x : RValue)
| fn (env : Environment) (params : List Ident) (body : Expr)

@[reducible, simp]
def EnvValue.toLookup (env : Environment) : EnvValue -> EnvLookup
| var x => .var x
| fn params body => .fn env params body

@[reducible, simp]
def Environment.lookup (x : Ident) (mem : Memory)
: Environment -> Except Error EnvLookup
| empty => .error .name
| closure b =>
  match mem b with
  | .closure xs _ _ => do
    let x <- (xs.lookup x).toExcept .name
    return x.toLookup (closure b)
  | _ => .error .metatheory
| scope xs env =>
  match xs.lookup x with
  | .some x => .ok $ x.toLookup (scope xs env)
  | .none => env.lookup x mem

@[reducible]
instance : CoeFun Environment (fun _ => Ident -> Memory -> Except Error EnvLookup) where
  coe env := env.lookup

@[reducible, simp]
def Environment.assign (x : Ident) (y : RValue) (mem : Memory)
: Environment -> Except Error (Environment × Memory)
| empty => .error .name
| closure b => do
  match mem b with
  | .closure xs params body =>
    match xs.lookup x with
    | .some (.var _) =>
      let xs := xs.insert x $ .var y
      let mem := mem.assign b $ .closure xs params body
      .ok (closure b, mem)
    | _ => .error .name
  | _ => .error .metatheory
| scope xs env =>
  match xs.lookup x with
  | .some (.var _) =>
    .ok (env.scope $ xs.insert x (.var y), mem)
  | .some (.fn _ _) => .error .name
  | .none => do
    let (env, mem) <- env.assign x y mem
    return (env.scope xs, mem)

@[reducible, simp]
def Environment.close (mem : Memory)
: Environment -> Option SimpleEnv
| empty => .some ∅
| closure box =>
  match mem box with
  | .closure env _ _ => .some env
  | _ => .none
| scope xs env => do
  let env <- env.close mem
  return xs ∪ env

@[reducible, simp]
def Environment.pop
: Environment -> Option Environment
| empty => .none
| closure _ => .none
| scope _ env => .some env

structure State where
  env : Environment
  mem : Memory

@[reducible]
def State.allocWith (x : BoxValue) (st : State) : Box × State :=
  let (box, mem) := st.mem.allocWith x
  (box, { st with mem := mem })

@[reducible]
def State.pushEnv (st : State) (env : SimpleEnv) : State where
  env := st.env.scope env
  mem := st.mem

@[reducible]
def State.popEnv (st : State) : Option State := do
  let env <- st.env.pop
  return { st with env }

inductive LValue where
| var (x : Ident)
| elem (b : Box) (i : ℕ)
deriving Repr, DecidableEq, Inhabited, Hashable

inductive Value where
| rvalue (x : RValue)
| lvalue (x : LValue)
deriving Repr, DecidableEq, Inhabited, Hashable

@[reducible, simp]
def Value.toRValue? : Value -> Option RValue
| .rvalue x => .some x
| .lvalue _ => .none

@[reducible]
def Value.toInt? (x : Value) : Except Error Int := do
  let x <- x.toRValue?.toExcept .lvalue
  x.toInt?.toExcept .type

@[reducible]
def Value.toNat? (x : Value) : Except Error Nat := do
  let x <- x.toRValue?.toExcept .lvalue
  x.toNat?

@[reducible]
def Value.toBool? (x : Value) : Except Error Bool := do
  let x <- x.toRValue?.toExcept .lvalue
  x.toBool?.toExcept .type

@[reducible]
def Value.toBox? (x : Value) : Except Error Box := do
  let x <- x.toRValue?.toExcept .lvalue
  x.toBox?.toExcept .type

@[reducible, simp]
def Value.toLValue? : Value -> Option LValue
| .lvalue x => .some x
| .rvalue _ => .none

inductive Result (V : Type) where
| ok (x : V) (st : State)
| err (err : Error)
deriving Inhabited

@[reducible, simp]
def Result.popEnv : Result Value -> Result Value
| ok (.lvalue (.var x)) st =>
  match st.env with
  | .scope xs _ =>
    if x ∈ xs then .err .lvalue
    else match st.popEnv with
    | .none => .err .metatheory
    | .some st => .ok (.lvalue $ .var x) st
  | _ =>
    match st.popEnv with
    | .none => .err .metatheory
    | .some st => .ok (.lvalue $ .var x) st
| ok x st =>
  match st.popEnv with
  | .none => .err .metatheory
  | .some st => ok x st
| res => res

@[reducible, simp]
def Result.toExcept {V : Type}
: Result V -> Except Error (V × State)
| ok x st => .ok (x, st)
| err e => .error e

@[reducible, simp]
def Result.ofExcept {V : Type}
: Except Error (V × State) -> Result V
| .ok (x, st) => .ok x st
| .error e => .err e

@[reducible]
def evalVar (st : State) (x : Ident) : Except Error (RValue × State) := do
  match <- st.env x st.mem with
  | .var x => return (x, st)
  | .fn env params body =>
    let env <- (env.close st.mem).toExcept .metatheory
    let (box, st) := st.allocWith $ .closure env params body
    return (.box box, st)

@[reducible]
def checkRef (st : State) (x : Ident) : Option Error :=
  match st.env x st.mem with
  | .ok (.var _) => .none
  | .ok _ => .some .name
  | .error e => .some e

@[reducible, simp]
def evalBinop (x y : Value) :  Binop -> Except Error RValue
| .or => do
  let x <- x.toBool?
  let y <- y.toBool?
  return .int (x || y).toInt
| .and => do
  let x <- x.toBool?
  let y <- y.toBool?
  return .int (x && y).toInt
| .eq => do
  let x <- x.toRValue?.toExcept .lvalue
  let y <- y.toRValue?.toExcept .lvalue
  return .int (x = y : Bool).toInt
| .ne => do
  let x <- x.toRValue?.toExcept .lvalue
  let y <- y.toRValue?.toExcept .lvalue
  return .int (x ≠ y : Bool).toInt
| .le => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int (x ≤ y : Bool).toInt
| .lt => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int (x < y : Bool).toInt
| .ge => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int (x ≥ y : Bool).toInt
| .gt => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int (x > y : Bool).toInt
| .add => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int $ x + y
| .sub => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int $ x - y
| .mul => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int $ x * y
| .quot => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int $ x.tdiv y
| .rem => do
  let x <- x.toInt?
  let y <- y.toInt?
  return .int $ x.tmod y

@[reducible]
def evalElem (mem : Memory) (x y : Value) : Except Error RValue := do
  let x <- x.toBox?
  let y <- y.toNat?
  match mem x with
  | .str xs =>
    let z <- xs[y]?.toExcept .runtime
    return .int z.toNat
  | .arr xs => xs[y]?.toExcept .runtime
  | .sexp _ xs => xs[y]?.toExcept .runtime
  | .closure _ _ _ => .error .type

@[reducible]
def evalElemRefR (mem : Memory) (x y : RValue) : Except Error LValue := do
  let x <- x.toBox?.toExcept .type
  let y <- y.toNat?
  match mem x with
  | .str xs =>
    if y < xs.size then return .elem x y
    else .error .runtime
  | .arr xs =>
    if y < xs.length then return .elem x y
    else .error .runtime
  | .sexp _ xs =>
    if y < xs.length then return .elem x y
    else .error .runtime
  | .closure _ _ _ => .error .type

@[reducible]
def evalElemRef (mem : Memory) (x y : Value) : Except Error LValue := do
  let x <- x.toRValue?.toExcept .lvalue
  let y <- y.toRValue?.toExcept .lvalue
  evalElemRefR mem x y

@[reducible]
def prepareCall (mem : Memory) (x : Value) (xs : List RValue)
: Except Error (State × Expr) := do
  let x <- x.toBox?
  match mem x with
  | .closure _ params body =>
    let args := List.zip params xs
    if args.length < params.length
    then .error .type
    else
      let env := List.foldl (fun acc (x, y) => acc.insert x (.var y)) ∅ args
      let st := { env := (Environment.closure x).scope env, mem }
      return (st, body)
  | _ => .error .type

@[reducible]
def commitCall (env : Environment) (mem : Memory) (x : Value)
: Result Value :=
  match x.toRValue? with
  | .some x => .ok (.rvalue x) { env, mem }
  | .none => .err .lvalue

@[reducible]
def evalAssignR (st : State) (x : Value) (y : RValue)
: Except Error State := do
  match <- x.toLValue?.toExcept .lvalue with
  | .var x =>
    let (env, mem) <- st.env.assign x y st.mem
    return { mem, env }
  | .elem x i =>
    let y <- (st.mem x).assign i y
    return { st with mem := st.mem.assign x y }

@[reducible]
def evalAssign (st : State) (x y : Value)
: Except Error (State × RValue) := do
  let y <- y.toRValue?.toExcept .lvalue
  let st <- evalAssignR st x y
  return (st, y)

mutual

@[reducible, simp]
def evalPattern (mem : Memory) (x : RValue)
: Pattern -> Option SimpleEnv
| .wildcard => .some ∅
| .const n =>
  if x = .int n then .some ∅
  else .none
| .string s => do
  match mem (<- x.toBox?) with
  | .str x =>
    if x = s.toByteArray then .some ∅
    else .none
  | _ => .none
| .array ps => do
  match mem (<- x.toBox?) with
  | .arr xs => evalPatternList mem xs ps
  | _ => .none
| .sexp t ps => do
  match mem (<- x.toBox?) with
  | .sexp s xs =>
    if t = s then evalPatternList mem xs ps
    else .none
  | _ => .none
| .named y p => do
  let env <- evalPattern mem x p
  return env.insert y $ .var x
| .boxTag =>
  match x with
  | .box _ => .some ∅
  | _ => .none
| .valTag =>
  match x with
  | .int _ => .some ∅
  | _ => .none
| .strTag => do
  let x <- x.toBox?
  match mem x with
  | .str _ => .some ∅
  | _ => .none
| .sexpTag => do
  let x <- x.toBox?
  match mem x with
  | .sexp _ _ => .some ∅
  | _ => .none
| .arrayTag => do
  let x <- x.toBox?
  match mem x with
  | .arr _ => .some ∅
  | _ => .none
| .funTag => do
  let x <- x.toBox?
  match mem x with
  | .closure _ _ _ => .some ∅
  | _ => .none

@[reducible, simp]
def evalPatternList (mem : Memory)
: List RValue -> List Pattern -> Option SimpleEnv
| [], [] => .some ∅
| x::xs, p::ps => do
  let env₁ <- evalPattern mem x p
  let env₂ <- evalPatternList mem xs ps
  return env₂ ∪ env₁
| _, _ => .none

end

@[reducible, simp]
def chooseCaseR (mem : Memory) (x : RValue)
: List (Pattern × Expr) -> Option (SimpleEnv × Expr)
| [] => .none
| (p, e)::bs =>
  match evalPattern mem x p with
  | .some env => .some (env, e)
  | .none => chooseCaseR mem x bs

@[reducible]
def chooseCase (mem : Memory) (x : Value) (bs : List (Pattern × Expr))
: Except Error (SimpleEnv × Expr) := do
  let x <- x.toRValue?.toExcept .lvalue
  (chooseCaseR mem x bs).toExcept .runtime -- or .type ???

@[reducible, simp]
def prepareDefList : List Definition -> SimpleEnv × Expr
| [] => (∅, .skip)
| .var x y :: ds =>
  let (env, e) := prepareDefList ds
  let env :=
    if x ∈ env then env
    else env.insert x $ .var $ .int 0
  (env, .seq (.assign (.ref x) y) e)
| .fn x xs body :: ds =>
  let (env, e) := prepareDefList ds
  let env :=
    if x ∈ env then env
    else env.insert x $ .fn xs body
  (env, e)

mutual

inductive Eval : State -> Expr -> Result Value -> Prop where
| skip st : Eval st .skip (.ok (.rvalue $ .int 0) st)
| varOk st st' x y
  : evalVar st x = .ok (y, st')
 -> Eval st (.var x) (.ok (.rvalue y) st')
| varErr st x e
  : evalVar st x = .error e
 -> Eval st (.var x) (.err e)
| refOk st x
  : checkRef st x = .none
 -> Eval st (.ref x) (.ok (.lvalue (.var x)) st)
| refErr st x e
  : checkRef st x = .some e
 -> Eval st (.ref x) (.err e)
| int st n : Eval st (.int n) (.ok (.rvalue $ .int n) st)
| str st st' s box
  : st.allocWith (.str s.toByteArray) = (box, st')
 -> Eval st (.str s) (.ok (.rvalue $ .box box) st')
| arrOk st₁ st₂ st₃ xs ys box
  : EvalList st₁ xs (.ok ys st₂)
 -> st₂.allocWith (.arr ys) = (box, st₃)
 -> Eval st₁ (.arr xs) (.ok (.rvalue $ .box box) st₃)
| arrErr st xs e
  : EvalList st xs (.err e)
 -> Eval st (.arr xs) (.err e)
| sexpOk st₁ st₂ st₃ t xs ys box
  : EvalList st₁ xs (.ok ys st₂)
 -> st₂.allocWith (.sexp t ys) = (box, st₃)
 -> Eval st₁ (.sexp t xs) (.ok (.rvalue $ .box box) st₃)
| sexpErr st t xs e
  : EvalList st xs (.err e)
 -> Eval st (.sexp t xs) (.err e)
| lambdaOk st st' xs x box env
  : st.env.close st.mem = .some env
 -> st.allocWith (.closure env xs x) = (box, st')
 -> Eval st (.lambda xs x) (.ok (.rvalue $ .box box) st')
| lambdaErr st xs x
  : st.env.close st.mem = .none
 -> Eval st (.lambda xs x) (.err .metatheory)
| binopOk st₁ st₂ st₃ op x₁ x₂ y₁ y₂ z
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalBinop y₁ y₂ op = .ok z
 -> Eval st₁ (.binop op x₁ x₂) (.ok (.rvalue z) st₃)
| binopErr st₁ st₂ st₃ op x₁ x₂ y₁ y₂ e
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalBinop y₁ y₂ op = (.error e)
 -> Eval st₁ (.binop op x₁ x₂) (.err e)
| binopErrL st op x₁ x₂ e
  : Eval st x₁ (.err e)
 -> Eval st (.binop op x₁ x₂) (.err e)
| binopErrR st st' op x₁ x₂ y₁ e
  : Eval st x₁ (.ok y₁ st')
 -> Eval st' x₂ (.err e)
 -> Eval st (.binop op x₁ x₂) (.err e)
| elemOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalElem st₃.mem y₁ y₂ = .ok z
 -> Eval st₁ (.elem x₁ x₂) (.ok (.rvalue z) st₃)
| elemErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalElem st₃.mem y₁ y₂ = .error e
 -> Eval st₁ (.elem x₁ x₂) (.err e)
| elemErrL st x₁ x₂ e
  : Eval st x₁ (.err e)
 -> Eval st (.elem x₁ x₂) (.err e)
| elemErrR st st' x₁ x₂ y₁ e
  : Eval st x₁ (.ok y₁ st')
 -> Eval st' x₂ (.err e)
 -> Eval st (.elem x₁ x₂) (.err e)
| elemRefOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalElemRef st₃.mem y₁ y₂ = .ok z
 -> Eval st₁ (.elemRef x₁ x₂) (.ok (.lvalue z) st₃)
| elemRefErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalElemRef st₃.mem y₁ y₂ = .error e
 -> Eval st₁ (.elemRef x₁ x₂) (.err e)
| elemRefErrL st x₁ x₂ e
  : Eval st x₁ (.err e)
 -> Eval st (.elemRef x₁ x₂) (.err e)
| elemRefErrR st st' x₁ x₂ y₁ e
  : Eval st x₁ (.ok y₁ st')
 -> Eval st' x₂ (.err e)
 -> Eval st (.elemRef x₁ x₂) (.err e)
| callOk st₁ st₂ st₃ st₄ st₅ x xs y ys z z'
  : Eval st₁ x (.ok y st₂)
 -> EvalList st₂ xs (.ok ys st₃)
 -> prepareCall st₃.mem y ys = .ok (st₄, z)
 -> Eval st₄ z (.ok z' st₅)
 -> Eval st₁ (.call x xs) (commitCall st₃.env st₅.mem z')
| callErr₁ st x xs e
  : Eval st x (.err e)
 -> Eval st (.call x xs) (.err e)
| callErr₂ st st' x xs y e
  : Eval st x (.ok y st')
 -> EvalList st' xs (.err e)
 -> Eval st (.call x xs) (.err e)
| callErr₃ st₁ st₂ st₃ x xs y ys e
  : Eval st₁ x (.ok y st₂)
 -> EvalList st₂ xs (.ok ys st₃)
 -> prepareCall st₃.mem y ys = .error e
 -> Eval st₁ (.call x xs) (.err e)
| callErr₄ st₁ st₂ st₃ st₄ x xs y ys z e
  : Eval st₁ x (.ok y st₂)
 -> EvalList st₂ xs (.ok ys st₃)
 -> prepareCall st₃.mem y ys = .ok (st₄, z)
 -> Eval st₄ z (.err e)
 -> Eval st₁ (.call x xs) (.err e)
| assignOk st₁ st₂ st₃ st₄ x₁ x₂ y₁ y₂ z
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalAssign st₃ y₁ y₂ = .ok (st₄, z)
 -> Eval st₁ (.assign x₁ x₂) (.ok (.rvalue z) st₄)
| assignErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalAssign st₃ y₁ y₂ = .error e
 -> Eval st₁ (.assign x₁ x₂) (.err e)
| assignErrL st x₁ x₂ e
  : Eval st x₁ (.err e)
 -> Eval st (.assign x₁ x₂) (.err e)
| assignErrR st st' x₁ x₂ y₁ e
  : Eval st x₁ (.ok y₁ st')
 -> Eval st' x₂ (.err e)
 -> Eval st (.assign x₁ x₂) (.err e)
| seqOk st₁ st₂ x₁ x₂ y₁ res
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ res
 -> Eval st₁ (.seq x₁ x₂) res
| seqErr st x₁ x₂ e
  : Eval st x₁ (.err e)
 -> Eval st (.seq x₁ x₂) (.err e)
| iteThen st st' x₁ x₂ x₃ y₁ res
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .ok true
 -> Eval st' x₂ res
 -> Eval st (.ite x₁ x₂ x₃) res
| iteElse st st' x₁ x₂ x₃ y₁ res
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .ok false
 -> Eval st' x₃ res
 -> Eval st (.ite x₁ x₂ x₃) res
| iteErr₁ st x₁ x₂ x₃ e
  : Eval st x₁ (.err e)
 -> Eval st (.ite x₁ x₂ x₃) (.err e)
| iteErr₂ st st' x₁ x₂ x₃ y₁ e
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .error e
 -> Eval st (.ite x₁ x₂ x₃) (.err e)
| loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> y₁.toBool? = .ok true
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> Eval st₃ (.loop x₁ x₂) res
 -> Eval st₁ (.loop x₁ x₂) res
| loopStop st st' x₁ x₂ y₁
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .ok false
 -> Eval st (.loop x₁ x₂) (.ok (.rvalue $ .int 0) st')
| loopErr st st' x₁ x₂ y₁ e
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .error e
 -> Eval st (.loop x₁ x₂) (.err e)
| loopErrL st x₁ x₂ e
  : Eval st x₁ (.err e)
 -> Eval st (.loop x₁ x₂) (.err e)
| loopErrR st st' x₁ x₂ y₁ e
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .ok true
 -> Eval st' x₂ (.err e)
 -> Eval st (.loop x₁ x₂) (.err e)
| caseOk st st' x₁ bs y₁ env x₂ res
  : Eval st x₁ (.ok y₁ st')
 -> chooseCase st'.mem y₁ bs = .ok (env, x₂)
 -> Eval (st'.pushEnv env) x₂ res
 -> Eval st (.case x₁ bs) res.popEnv
| caseErr₁ st x₁ bs e
  : Eval st x₁ (.err e)
 -> Eval st (.case x₁ bs) (.err e)
| caseErr₂ st st' x₁ bs y₁ e
  : Eval st x₁ (.ok y₁ st')
 -> chooseCase st'.mem y₁ bs = .error e
 -> Eval st (.case x₁ bs) (.err e)
| scope st x₁ env x₂ res
  : prepareDefList x₁.defs = (env, x₂)
 -> Eval (st.pushEnv env) (.seq x₂ x₁.body) res
 -> Eval st (.scope x₁) res.popEnv

inductive EvalList : State -> List Expr -> Result (List RValue) -> Prop where
| nil st : EvalList st [] (.ok [] st)
| cons st₁ st₂ st₃ x xs y ys
  : Eval st₁ x (.ok (.rvalue y) st₂)
 -> EvalList st₂ xs (.ok ys st₃)
 -> EvalList st₁ (x::xs) (.ok (y::ys) st₃)
| err st st' x xs y
  : Eval st x (.ok (.lvalue y) st')
 -> EvalList st (x::xs) (.err .lvalue)
| errL st x xs e
  : Eval st x (.err e)
 -> EvalList st (x::xs) (.err e)
| errR st st' x xs y e
  : Eval st x (.ok y st')
 -> EvalList st' xs (.err e)
 -> EvalList st (x::xs) (.err e)

end
