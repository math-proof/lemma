import Def.Lean.Name
import Def.Lean.BinderInfo.Part2
import Instance.Lean.Meta.Expr
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


def Lean.Expr.toString (e : Expr) : String :=
  ToString.toString e


def Lean.Expr.declName (e : Expr) : Name :=
  match e with
  | .app e _ => e.declName
  | .const declName _ => declName
  | _ => default


def Lean.Expr.binderInfos (e : Expr) : List BinderInfo :=
  match e with
  | .forallE _ _ body bi =>
    bi :: body.binderInfos
  | _  =>
    []


def Lean.BinderInfo.toBinder : BinderInfo → Binder
  | .default => Binder.default
  | .implicit => Binder.implicit
  | .strictImplicit => Binder.strictImplicit
  | .instImplicit => Binder.instImplicit

def Lean.Name.binderInfo (name : Name) : MetaM (List BinderInfo) := do
  (·.binderInfos) <$> name.toExpr


def Lean.Expr.binderTypes (e : Expr) : List Expr :=
  match e with
  | .forallE _ binderType body _ =>
    binderType :: body.binderTypes
  | _  =>
    []

def Lean.Name.binderType (name : Name) : MetaM (List Expr) := do
  (·.binderTypes) <$> name.toExpr


def Lean.Name.is_Lemma (name : Name) : MetaM Bool := do
  return match ← name.toConstantInfo with
  | .axiomInfo _
  | .thmInfo _ => true
  | _ => false


partial def Lean.Expr.subs (e : Expr) (fvarId : FVarId) (deBruijnIndex : Nat) : MetaM Expr := do
  match e with
  | .bvar _
  | .sort _
  | .const ..
  | .lit _ =>
    return e

  | .fvar fvarId' =>
    if fvarId == fvarId' then
      return .bvar deBruijnIndex
    else
      return e

  | .mvar mvarId  =>
    if let some e' ← Lean.getExprMVarAssignment? mvarId then
      let e'' ← e'.subs fvarId deBruijnIndex
      if e'' == e' then
        return e
      else
        return e''
    else
      return e

  | .app fn arg =>
    let fn' ← fn.subs fvarId deBruijnIndex
    let arg' ← arg.subs fvarId deBruijnIndex
    if fn == fn' && arg == arg' then
      return e
    else
      return .app fn' arg'

  | .lam binderName binderType body binderInfo =>
    let binderType' ← binderType.subs fvarId deBruijnIndex
    let body' ← body.subs fvarId (deBruijnIndex + 1)
    if binderType == binderType' && body == body' then
      return e
    else
      return .lam binderName binderType' body' binderInfo

  | .forallE binderName binderType body binderInfo =>
    let binderType' ← binderType.subs fvarId deBruijnIndex
    let body' ← body.subs fvarId (deBruijnIndex + 1)
    if binderType == binderType' && body == body' then
      return e
    else
      return .forallE binderName binderType' body' binderInfo

  | .letE declName type value body nonDep =>
    let type' ← type.subs fvarId deBruijnIndex
    let value' ← value.subs fvarId deBruijnIndex
    let body' ← body.subs fvarId (deBruijnIndex + 1)
    if type == type' && value == value' && body == body' then
      return e
    else
      return .letE declName type' value' body' nonDep

  | .mdata data e =>
    let e' ← e.subs fvarId deBruijnIndex
    if e == e' then
      return e
    else
      return .mdata data e'

  | .proj typeName idx e =>
    let e' ← e.subs fvarId deBruijnIndex
    if e == e' then
      return e
    else
      return .proj typeName idx e'


partial def Lean.Expr.contains (e : Expr) (name : Name) : MetaM Bool := do
  match e with
  | .bvar _
  | .sort _
  | .const ..
  | .lit _ =>
    return false

  | .fvar fvarId =>
    if let some decl ← fvarId.findDecl? then
      return decl.userName == name
    else
      return false

  | .mvar mvarId  =>
    if let some e ← Lean.getExprMVarAssignment? mvarId then
      e.contains name
    else
      return false

  | .app fn arg =>
    return (← fn.contains name) || (← arg.contains name)

  | .lam _ _ body _
  | .forallE _ _ body _
  | .letE _ _ _ body _ =>
    body.contains name

  | .mdata _ e
  | .proj _ _ e =>
    e.contains name


def Lean.Expr.isIntDiv (e : Expr) : Bool :=
  if let .app (.app (.app (.app (.app (.app (.const `HDiv.hDiv _) _) _) _) (.app _ arg)) _) _ := e then
    match arg with
    | .const `Int.instDiv _
    | .app (.app (.const `IntegerRing.toDiv _) _) _ => true
    | _ => false
  else
    false

def Lean.Expr.extract_conditions (e : Expr) (n : Nat) (list : List Expr) : List Expr :=
  match n with
  | 0 =>
    list
  | n + 1 =>
    if let .app fn arg := e then
      fn.extract_conditions n (arg :: list)
    else
      list

def Lean.Expr.mapDeBruijnIndex (h : Nat → Nat → Expr) (offset : Nat) : Expr → Expr
  | bvar deBruijnIndex =>
    h deBruijnIndex offset
  | app fn arg =>
    app (fn.mapDeBruijnIndex h offset) (arg.mapDeBruijnIndex h offset)
  | lam binderName binderType body binderInfo =>
    lam binderName (binderType.mapDeBruijnIndex h offset) (body.mapDeBruijnIndex h offset.succ) binderInfo
  | forallE binderName binderType body binderInfo =>
    forallE binderName (binderType.mapDeBruijnIndex h offset) (body.mapDeBruijnIndex h offset.succ) binderInfo
  | letE declName type value body nondep =>
    letE declName (type.mapDeBruijnIndex h offset) (value.mapDeBruijnIndex h offset) (body.mapDeBruijnIndex h offset.succ) nondep
  | mdata data expr =>
    mdata data (expr.mapDeBruijnIndex h offset)
  | proj typeName idx struct =>
    proj typeName idx (struct.mapDeBruijnIndex h offset)
  | e => e

def Lean.Expr.setDeBruijnIndex (e : Expr) (old : Nat) (new : Nat) : Expr :=
  e.mapDeBruijnIndex (fun deBruijnIndex offset => if deBruijnIndex == old + offset then bvar (new + offset) else bvar deBruijnIndex) 0

def Lean.Expr.incDeBruijnIndex (e : Expr) (n : Nat) (offset : Nat := 0): Expr :=
  e.mapDeBruijnIndex (fun deBruijnIndex offset => if deBruijnIndex ≥ offset then bvar (deBruijnIndex + n) else bvar deBruijnIndex) offset

def Lean.Expr.decDeBruijnIndex (e : Expr) (n : Nat) (offset : Nat := 0): Expr :=
  e.mapDeBruijnIndex (fun deBruijnIndex offset => if deBruijnIndex ≥ offset then bvar (deBruijnIndex - n) else bvar deBruijnIndex) offset

/--
  Construct a nested application expression from a function and a list of arguments.
  `f.mkApp [a, b, c]` becomes `((f a) b) c`.
-/
def Lean.Expr.mkApp (f : Expr) (args : List Expr) : Expr :=
  args.foldl Lean.mkApp f

def Lean.Expr.comm : Expr → Expr
  | .app (.app (.app (.const `Eq us) α) a) b =>
    (Expr.const `Eq us).mkApp [α, b, a]
  | .app (.app (.const `Iff us) a) b =>
    (Expr.const `Iff us).mkApp [b, a]
  | .app (.app (.app (.app (.app (.app (.const `SEq us) α) Vector) n) m) a) b =>
    (Expr.const `SEq us).mkApp [α, Vector, m, n, b, a]
  | .app (.app (.app (.app (.const `HEq us) α) a) β) b =>
    (Expr.const `HEq us).mkApp [β, b, α, a]
  | .app (.app (.app (.const `Ne us) α) a) b =>
    (Expr.const `Ne us).mkApp [α, b, a]
  | .app (.app (.app (.app (.const `LT.lt us) α) I) a) b =>
    (Expr.const `GT.gt us).mkApp [α, I, b, a]
  | .app (.app (.app (.app (.const `LE.le us) α) I) a) b =>
    (Expr.const `GE.ge us).mkApp [α, I, b, a]
  | .app (.app (.app (.app (.const `GT.gt us) α) I) a) b =>
    (Expr.const `LT.lt us).mkApp [α, I, b, a]
  | .app (.app (.app (.app (.const `GE.ge us) α) I) a) b =>
    (Expr.const `LE.le us).mkApp [α, I, b, a]
  | .app (.app (.const `And us) a) b =>
    (Expr.const `And us).mkApp [b, a]
  | .app (.app (.const `Or us) a) b =>
    (Expr.const `Or us).mkApp [b, a]
  | .app (.app (.app (.app (.const `HasEquiv.Equiv us) α) self) a) b =>
    (Expr.const `HasEquiv.Equiv us).mkApp [α, self, b, a]
  | .app (.app (.app (.const `Nat.ModEq us) n) a) b =>
    (Expr.const `Nat.ModEq us).mkApp [n, b, a]
  | .app (.const `Not usNot) p =>
    (Expr.const `Not usNot).mkApp [p.comm]
  | .forallE n t b i =>
    .forallE n t b.comm i
  | .lam n t b i =>
    .lam n t b.comm i
  | .app (.app (.app (.const `Filter.Eventually us) α) p) f =>
    (Expr.const `Filter.Eventually us).mkApp [α, p.comm, f]
  | .app (.app (.app (.const `Filter.EventuallyEq us) l) f) g =>
    (Expr.const `Filter.EventuallyEq us).mkApp [l, g, f]
  | e  =>
    panic! s!"Expected an operator of Eq, Iff, SEq, HEq, Ne, Lt, Le, Gt, Ge, And, Or, Not, ModEq, Eventually, EventuallyEq, but got {e.ctorName} :\n{e}"

