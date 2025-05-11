import stdlib.Lean.Name
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


def Lean.Expr.is_Prop (e : Expr) : MetaM Bool := do
  match e with
  | .app e_fn _ =>
    if let .forallE _ _ body _ ← inferType e_fn then
      return body.isProp

  | .forallE (body := body) .. =>
    return body.isProp

  | .fvar fvarId =>
    if let some decl ← fvarId.findDecl? then
      return decl.type.isProp

  | _  =>
    pure ()

  return false


inductive Binder where
  /-- explicit binder annotation for proposition, e.g. `(h : Prop)` -/
  | given
  /-- Default binder annotation, e.g. `(x : α)` -/
  | default
  /-- Implicit binder annotation, e.g., `{x : α}` -/
  | implicit
  /-- Strict implicit binder annotation, e.g., `{{ x : α }}` -/
  | strictImplicit
  /-- Local instance binder annotataion, e.g., `[Decidable α]` -/
  | instImplicit
  /-- membership binder annotation, e.g. `x ∈ α` -/
  | contains
  deriving Inhabited, BEq, Repr, CtorName

def Binder.toString : Binder → String := CtorName.ctorName


instance : ToString Binder where
  toString := Binder.toString


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


def Lean.Expr.extract_conditions_recursively (e : Expr) (n : Nat) (array : List Expr) : List Expr :=
  match n with
  | .zero =>
    array
  | .succ n =>
    if let .app fn arg := e then
      fn.extract_conditions_recursively n (arg :: array)
    else
      array


def Lean.Expr.extract_conditions (e : Expr) (n : Nat) : List Expr :=
  if let .forallE _ _ body .default := e then
    body.extract_conditions_recursively n []
  else
    []
