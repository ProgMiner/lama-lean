import Mathlib

import Lama.Ast


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
def RValue.toNat? (x : RValue) : Option ℕ := do
  let x <- x.toInt?
  x.toNat?

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
: BoxValue -> Option BoxValue
| str xs => do
  let x <- x.toNat?
  let xs <- xs.set? i x.toUInt8
  return str xs
| arr xs => do
  let xs <- xs.set? i x
  return arr xs
| sexp t xs => do
  let xs <- xs.set? i x
  return sexp t xs
| closure _ _ _ => .none

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
: Environment -> Option EnvLookup
| empty => .none
| closure b =>
  match mem b with
  | .closure xs _ _ => do
    let x <- xs.lookup x
    return x.toLookup (closure b)
  | _ => .none
| scope xs env =>
  match xs.lookup x with
  | .some x => .some $ x.toLookup (scope xs env)
  | .none => env.lookup x mem

@[reducible]
instance : CoeFun Environment (fun _ => Ident -> Memory -> Option EnvLookup) where
  coe env := env.lookup

@[reducible, simp]
def Environment.assign (x : Ident) (y : RValue) (mem : Memory)
: Environment -> Option (Environment × Memory)
| empty => .none
| closure b => do
  match mem b with
  | .closure xs params body =>
    match xs.lookup x with
    | .some (.var _) =>
      let xs := xs.insert x $ .var y
      let mem := mem.assign b $ .closure xs params body
      .some (closure b, mem)
    | _ => .none
  | _ => .none
| scope xs env =>
  match xs.lookup x with
  | .some (.var _) =>
    .some (env.scope $ xs.insert x (.var y), mem)
  | .some (.fn _ _) => .none
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
def Environment.pop : Environment -> Environment
| empty => empty
| closure _ => empty
| scope _ env => env

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
def State.popEnv (st : State) : State where
  env := st.env.pop
  mem := st.mem

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
def Value.toInt? (x : Value) : Option Int := do
  (<- x.toRValue?).toInt?

@[reducible]
def Value.toNat? (x : Value) : Option Nat := do
  (<- x.toRValue?).toNat?

@[reducible]
def Value.toBool? (x : Value) : Option Bool := do
  (<- x.toRValue?).toBool?

@[reducible]
def Value.toBox? (x : Value) : Option Box := do
  (<- x.toRValue?).toBox?

@[reducible, simp]
def Value.toLValue? : Value -> Option LValue
| .lvalue x => .some x
| .rvalue _ => .none

inductive Result (V : Type) where
| ok (x : V) (st : State)
| err
deriving Inhabited

@[reducible, simp]
def Result.popEnv : Result Value -> Result Value
| ok (.lvalue (.var x)) st =>
  match st.env with
  | .scope xs _ =>
    if x ∈ xs then .err
    else .ok (.lvalue $ .var x) st.popEnv
  | _ => .ok (.lvalue $ .var x) st.popEnv
| ok x st => ok x st.popEnv
| res => res

@[reducible]
def evalVar (st : State) (x : Ident) : Option (RValue × State) := do
  match <- st.env x st.mem with
  | .var x => return (x, st)
  | .fn env params body =>
    let env <- env.close st.mem
    let (box, st) := st.allocWith $ .closure env params body
    return (.box box, st)

@[reducible]
def checkRef (st : State) (x : Ident) : Bool :=
  match st.env x st.mem with
  | .some (.var _) => true
  | _ => false

@[reducible, simp]
def evalBinop (x y : Value) :  Binop -> Option RValue
| .or => do
  let x <- x.toBool?
  let y <- y.toBool?
  return .int (x || y).toInt
| .and => do
  let x <- x.toBool?
  let y <- y.toBool?
  return .int (x && y).toInt
| .eq => do
  let x <- x.toRValue?
  let y <- y.toRValue?
  return .int (x = y : Bool).toInt
| .ne => do
  let x <- x.toRValue?
  let y <- y.toRValue?
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
def evalElem (mem : Memory) (x y : Value) : Option RValue := do
  let x <- x.toBox?
  let y <- y.toNat?
  match mem x with
  | .str xs =>
    let z <- xs[y]?
    return .int z.toNat
  | .arr xs => xs[y]?
  | .sexp _ xs => xs[y]?
  | .closure _ _ _ => .none

@[reducible]
def evalElemRefR (mem : Memory) (x y : RValue) : Option LValue := do
  let x <- x.toBox?
  let y <- y.toNat?
  let ok : Bool := match mem x with
  | .str xs => y < xs.size
  | .arr xs => y < xs.length
  | .sexp _ xs => y < xs.length
  | .closure _ _ _ => false
  if ok then return .elem x y
  else .none

@[reducible]
def evalElemRef (mem : Memory) (x y : Value) : Option LValue := do
  evalElemRefR mem (<- x.toRValue?) (<- y.toRValue?)

@[reducible]
def prepareCall (mem : Memory) (x : Value) (xs : List RValue)
: Option (State × Expr) := do
  let x <- x.toBox?
  match mem x with
  | .closure _ params body =>
    let args := List.zip params xs
    if args.length < params.length then .none
    else
      let env := List.foldl (fun acc (x, y) => acc.insert x (.var y)) ∅ args
      let st := { env := (Environment.closure x).scope env, mem }
      return (st, body)
  | _ => .none

@[reducible]
def commitCall (env : Environment) (mem : Memory) (x : Value)
: Result Value :=
  match x.toRValue? with
  | .some x => .ok (.rvalue x) { env, mem }
  | .none => .err

@[reducible]
def evalAssignR (st : State) (x : Value) (y : RValue) : Option State := do
  match <- x.toLValue? with
  | .var x =>
    let (env, mem) <- st.env.assign x y st.mem
    return { mem, env }
  | .elem x i =>
    let y <- (st.mem x).assign i y
    return { st with mem := st.mem.assign x y }

@[reducible]
def evalAssign (st : State) (x y : Value) : Option (State × RValue) := do
  let y <- y.toRValue?
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
def chooseCase (mem : Memory) (x : Value) (bs : List (Pattern × Expr)) := do
  chooseCaseR mem (<- x.toRValue?) bs

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
  : evalVar st x = .some (y, st')
 -> Eval st (.var x) (.ok (.rvalue y) st')
| varErr st x
  : evalVar st x = .none
 -> Eval st (.var x) .err
| refOk st x
  : checkRef st x
 -> Eval st (.ref x) (.ok (.lvalue (.var x)) st)
| refErr st x
  : ¬ checkRef st x
 -> Eval st (.ref x) .err
| int st n : Eval st (.int n) (.ok (.rvalue $ .int n) st)
| str st st' s box
  : st.allocWith (.str s.toByteArray) = (box, st')
 -> Eval st (.str s) (.ok (.rvalue $ .box box) st')
| arrOk st₁ st₂ st₃ xs ys box
  : EvalList st₁ xs (.ok ys st₂)
 -> st₂.allocWith (.arr ys) = (box, st₃)
 -> Eval st₁ (.arr xs) (.ok (.rvalue $ .box box) st₃)
| arrErr st xs
  : EvalList st xs .err
 -> Eval st (.arr xs) .err
| sexpOk st₁ st₂ st₃ t xs ys box
  : EvalList st₁ xs (.ok ys st₂)
 -> st₂.allocWith (.sexp t ys) = (box, st₃)
 -> Eval st₁ (.sexp t xs) (.ok (.rvalue $ .box box) st₃)
| sexpErr st t xs
  : EvalList st xs .err
 -> Eval st (.sexp t xs) .err
| lambdaOk st st' xs x box env
  : st.env.close st.mem = .some env
 -> st.allocWith (.closure env xs x) = (box, st')
 -> Eval st (.lambda xs x) (.ok (.rvalue $ .box box) st')
| lambdaErr st xs x
  : st.env.close st.mem = .none
 -> Eval st (.lambda xs x) .err
| binopOk st₁ st₂ st₃ op x₁ x₂ y₁ y₂ z
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalBinop y₁ y₂ op = .some z
 -> Eval st₁ (.binop op x₁ x₂) (.ok (.rvalue z) st₃)
| binopErr st₁ st₂ st₃ op x₁ x₂ y₁ y₂
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalBinop y₁ y₂ op = .none
 -> Eval st₁ (.binop op x₁ x₂) .err
| binopErrL st op x₁ x₂
  : Eval st x₁ .err
 -> Eval st (.binop op x₁ x₂) .err
| binopErrR st st' op x₁ x₂ y₁
  : Eval st x₁ (.ok y₁ st')
 -> Eval st' x₂ .err
 -> Eval st (.binop op x₁ x₂) .err
| elemOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalElem st₃.mem y₁ y₂ = .some z
 -> Eval st₁ (.elem x₁ x₂) (.ok (.rvalue z) st₃)
| elemErr st₁ st₂ st₃ x₁ x₂ y₁ y₂
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalElem st₃.mem y₁ y₂ = .none
 -> Eval st₁ (.elem x₁ x₂) .err
| elemErrL st x₁ x₂
  : Eval st x₁ .err
 -> Eval st (.elem x₁ x₂) .err
| elemErrR st st' x₁ x₂ y₁
  : Eval st x₁ (.ok y₁ st')
 -> Eval st' x₂ .err
 -> Eval st (.elem x₁ x₂) .err
| elemRefOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalElemRef st₃.mem y₁ y₂ = .some z
 -> Eval st₁ (.elemRef x₁ x₂) (.ok (.lvalue z) st₃)
| elemRefErr st₁ st₂ st₃ x₁ x₂ y₁ y₂
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalElemRef st₃.mem y₁ y₂ = .none
 -> Eval st₁ (.elemRef x₁ x₂) .err
| elemRefErrL st x₁ x₂
  : Eval st x₁ .err
 -> Eval st (.elemRef x₁ x₂) .err
| elemRefErrR st st' x₁ x₂ y₁
  : Eval st x₁ (.ok y₁ st')
 -> Eval st' x₂ .err
 -> Eval st (.elemRef x₁ x₂) .err
| callOk st₁ st₂ st₃ st₄ st₅ x xs y ys z z'
  : Eval st₁ x (.ok y st₂)
 -> EvalList st₂ xs (.ok ys st₃)
 -> prepareCall st₃.mem y ys = .some (st₄, z)
 -> Eval st₄ z (.ok z' st₅)
 -> Eval st₁ (.call x xs) (commitCall st₃.env st₅.mem z')
| callErr₁ st x xs
  : Eval st x .err
 -> Eval st (.call x xs) .err
| callErr₂ st st' x xs y
  : Eval st x (.ok y st')
 -> EvalList st' xs .err
 -> Eval st (.call x xs) .err
| callErr₃ st₁ st₂ st₃ x xs y ys
  : Eval st₁ x (.ok y st₂)
 -> EvalList st₂ xs (.ok ys st₃)
 -> prepareCall st₃.mem y ys = .none
 -> Eval st₁ (.call x xs) .err
| callErr₄ st₁ st₂ st₃ st₄ x xs y ys z
  : Eval st₁ x (.ok y st₂)
 -> EvalList st₂ xs (.ok ys st₃)
 -> prepareCall st₃.mem y ys = .some (st₄, z)
 -> Eval st₄ z .err
 -> Eval st₁ (.call x xs) .err
| assignOk st₁ st₂ st₃ st₄ x₁ x₂ y₁ y₂ z
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalAssign st₃ y₁ y₂ = .some (st₄, z)
 -> Eval st₁ (.assign x₁ x₂) (.ok (.rvalue z) st₄)
| assignErr st₁ st₂ st₃ x₁ x₂ y₁ y₂
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> evalAssign st₃ y₁ y₂ = .none
 -> Eval st₁ (.assign x₁ x₂) .err
| assignErrL st x₁ x₂
  : Eval st x₁ .err
 -> Eval st (.assign x₁ x₂) .err
| assignErrR st st' x₁ x₂ y₁
  : Eval st x₁ (.ok y₁ st')
 -> Eval st' x₂ .err
 -> Eval st (.assign x₁ x₂) .err
| seqOk st₁ st₂ x₁ x₂ y₁ res
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> Eval st₂ x₂ res
 -> Eval st₁ (.seq x₁ x₂) res
| seqErr st x₁ x₂
  : Eval st x₁ .err
 -> Eval st (.seq x₁ x₂) .err
| iteThen st st' x₁ x₂ x₃ y₁ res
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .some true
 -> Eval st' x₂ res
 -> Eval st (.ite x₁ x₂ x₃) res
| iteElse st st' x₁ x₂ x₃ y₁ res
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .some false
 -> Eval st' x₃ res
 -> Eval st (.ite x₁ x₂ x₃) res
| iteErr₁ st x₁ x₂ x₃
  : Eval st x₁ .err
 -> Eval st (.ite x₁ x₂ x₃) .err
| iteErr₂ st st' x₁ x₂ x₃ y₁
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .none
 -> Eval st (.ite x₁ x₂ x₃) .err
| loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res
  : Eval st₁ x₁ (.ok y₁ st₂)
 -> y₁.toBool? = .some true
 -> Eval st₂ x₂ (.ok y₂ st₃)
 -> Eval st₃ (.loop x₁ x₂) res
 -> Eval st₁ (.loop x₁ x₂) res
| loopStop st st' x₁ x₂ y₁
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .some false
 -> Eval st (.loop x₁ x₂) (.ok (.rvalue $ .int 0) st')
| loopErr st st' x₁ x₂ y₁
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .none
 -> Eval st (.loop x₁ x₂) .err
| loopErrL st x₁ x₂
  : Eval st x₁ .err
 -> Eval st (.loop x₁ x₂) .err
| loopErrR st st' x₁ x₂ y₁
  : Eval st x₁ (.ok y₁ st')
 -> y₁.toBool? = .some true
 -> Eval st' x₂ .err
 -> Eval st (.loop x₁ x₂) .err
| caseOk st st' x₁ bs y₁ env x₂ res
  : Eval st x₁ (.ok y₁ st')
 -> chooseCase st'.mem y₁ bs = .some (env, x₂)
 -> Eval (st'.pushEnv env) x₂ res
 -> Eval st (.case x₁ bs) res.popEnv
| caseErr₁ st x₁ bs
  : Eval st x₁ .err
 -> Eval st (.case x₁ bs) .err
| caseErr₂ st st' x₁ bs y₁
  : Eval st x₁ (.ok y₁ st')
 -> chooseCase st'.mem y₁ bs = .none
 -> Eval st (.case x₁ bs) .err
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
 -> EvalList st (x::xs) .err
| errL st x xs
  : Eval st x .err
 -> EvalList st (x::xs) .err
| errR st st' x xs y
  : Eval st x (.ok y st')
 -> EvalList st' xs .err
 -> EvalList st (x::xs) .err

end
