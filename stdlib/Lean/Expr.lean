import stdlib.Lean.Name
import stdlib.Lean.BinderInfo
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
  | .zero =>
    list
  | .succ n =>
    if let .app fn arg := e then
      fn.extract_conditions n (arg :: list)
    else
      list

def Lean.Expr.mapDeBruijnIndex (h : Nat → Nat → Nat) (offset : Nat) : Expr → Expr
  | bvar deBruijnIndex =>
    bvar (h deBruijnIndex offset)
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
  e.mapDeBruijnIndex (fun deBruijnIndex offset => if deBruijnIndex == old + offset then new + offset else deBruijnIndex) 0

def Lean.Expr.incDeBruijnIndex (e : Expr) (n : Nat) (offset : Nat := 0): Expr :=
  e.mapDeBruijnIndex (fun deBruijnIndex offset => if deBruijnIndex ≥ offset then deBruijnIndex + n else deBruijnIndex) offset

def Lean.Expr.decDeBruijnIndex (e : Expr) (n : Nat) (offset : Nat := 0): Expr :=
  e.mapDeBruijnIndex (fun deBruijnIndex offset => if deBruijnIndex ≥ offset then deBruijnIndex - n else deBruijnIndex) offset

/--
  Construct a nested application expression from a function and a list of arguments.
  `f.mkApp [a, b, c]` becomes `((f a) b) c`.
-/
def Lean.Expr.mkApp (f : Expr) (args : List Expr) : Expr :=
  args.foldl Lean.mkApp f

def Lean.Expr.comm : Expr → Expr
  | .app (.app (.app (.const `Eq us) α) a) b =>
    -- Eq.{u} {α : Sort u} : α → α → Prop
    (Expr.const `Eq us).mkApp [α, b, a]
  | .app (.app (.const `Iff us) a) b =>
    -- Iff (a b : Prop) : Prop
    (Expr.const `Iff us).mkApp [b, a]
  | .app (.app (.app (.app (.app (.app (.const `SEq us) α) Vector) n) m) a) b =>
  -- SEq.{u, v} {α : Type u} {Vector : α → Sort v} {n m : α} (a : Vector n) (b : Vector m) : Prop
    (Expr.const `SEq us).mkApp [α, Vector, m, n, b, a]
  | .app (.app (.app (.app (.const `HEq us) α) a) β) b =>
  -- HEq.{u} {α : Sort u} : α → {β : Sort u} → β → Prop
    (Expr.const `HEq us).mkApp [β, b, α, a]
  | e  =>
    panic! s!"Expected an operator of Eq, Iff, SEq, or HEq, but got: {e}"

def Lean.Expr.symm : Expr → Expr
  | .app (.app (.app (.const `Eq us) α) a) b =>
    (Expr.const `Eq.symm us).mkApp [α, a, b]
  | .app (.app (.const `Iff us) a) b =>
    (Expr.const `Iff.symm us).mkApp [a, b]
  | .app (.app (.app (.app (.app (.app (.const `SEq us) α) Vector) n) m) a) b =>
    (Expr.const `SEq.symm us).mkApp [α, Vector, n, m, a, b]
  | .app (.app (.app (.app (.const `HEq us) α) a) β) b =>
    -- HEq.symm.{u} {α β : Sort u} {a : α} {b : β} (h : HEq a b) : HEq b a -- different from `HEq
    (Expr.const `HEq.symm us).mkApp [α, β, a, b]
  | e  =>
    panic! s!"Expected an operator of Eq, Iff, SEq, or HEq, but got: {e}"

def Lean.Expr.decomposeType : Expr → Expr × Expr
  | .app (.app (.app (.app (.const `letFun us) α) β) v) (.lam binderName binderType body binderInfo) =>
    let args := body.decomposeType
    ⟨
      (Expr.const `letFun us).mkApp [α, β, v, .lam binderName binderType args.fst binderInfo],
      .letE binderName binderType v args.snd false
    ⟩
  | .letE declName type value body false =>
    let fn := fun body => .letE declName type value body false
    body.decomposeType.map fn fn
  | e  =>
    ⟨e.comm, e.symm⟩

def Lean.Expr.decomposeIff : Expr → List Level × Expr × Expr
  | .app (.app (.const `Iff us) a) b =>
    ⟨us, a, b⟩
  | .app (.app (.app (.app (.const `Iff.intro us) _) _) mp) mpr =>
    ⟨us, mp, mpr⟩
  | e =>
    panic! s!"Body must be of the form `Iff a b`, got: {e}"

def Lean.Expr.decomposeAnd : Expr → List Expr × List Expr
  | .app (.app (.const `And _) a) b =>
    let ⟨curr, next⟩ := b.decomposeAnd
    ⟨a :: curr, b :: next⟩
  | e =>
    ⟨[e], []⟩

def Lean.Expr.decompose_lam (binders : List (Name × Expr × BinderInfo) := []) : Expr → (List (Name × Expr × BinderInfo)) × Expr
  | .lam binderName binderType body binderInfo =>
    body.decompose_lam (⟨binderName, binderType, binderInfo⟩ :: binders)
  | body =>
    ⟨binders, body⟩

def Lean.Expr.decompose_forallE (binders : List (Name × Expr × BinderInfo) := []) : Expr → (List (Name × Expr × BinderInfo)) × Expr
  | .forallE binderName binderType body binderInfo =>
    body.decompose_forallE (⟨binderName, binderType, binderInfo⟩ :: binders)
  | body =>
    ⟨binders, body⟩

def Lean.Expr.format (indent : Nat := 0) (is_indented : Bool := true): Expr → String
  | .lam binderName binderType body binderInfo =>
    let pairedGroup := binderInfo.pairedGroup
    let s := " ".repeat indent ++ "fun " ++ pairedGroup.fst ++ binderName.toString ++ " : " ++ binderType.format 0 false ++ pairedGroup.snd ++ " =>\n" ++
    body.format (indent + 4) true
    if is_indented then s else "\n" ++ s
  | .forallE binderName binderType body binderInfo =>
    let pairedGroup := binderInfo.pairedGroup
    let s := " ".repeat indent ++ "∀ " ++ pairedGroup.fst ++ binderName.toString ++ " : " ++ binderType.format 0 false ++ pairedGroup.snd ++ " =>\n" ++
    body.format (indent + 4) true
    if is_indented then s else "\n" ++ s
  | .letE declName type value body _ =>
    let s := " ".repeat indent ++ "let " ++ declName.toString ++ " : " ++ type.format 0 false ++ " := " ++ value.format 0 false ++ "\n" ++ body.format indent true
    if is_indented then s else "\n" ++ s
  | .bvar deBruijnIndex =>
    let s := s!"#{deBruijnIndex}"
    if is_indented then " ".repeat indent ++ s else s
  | app fn arg =>
    let fn := fn.format indent false
    let arg := arg.format indent false
    let s := s!".app ({fn}) ({arg})"
    if is_indented then " ".repeat indent ++ s else s
  | mdata _ expr =>
    let s := expr.format indent false
    if is_indented then " ".repeat indent ++ s else s
  | proj typeName idx struct =>
    let s := struct.format 0 false
    let s := s!"({s}).proj {typeName} {idx}"
    if is_indented then " ".repeat indent ++ s else s
  | e =>
    let s := e.toString
    if is_indented then " ".repeat indent ++ s else s

/--
Checks if the expression contains a specific bound variable (by de Bruijn index).
* `deBruijn`: The index to search for (relative to the current context).
* **Metavariables**: Returns `false` conservatively (cannot inspect assignments).
-/
def Lean.Expr.containsBVar (deBruijn : Nat) : Expr → Bool
  | forallE _ binderType body _
  | lam _ binderType body _ =>
    binderType.containsBVar deBruijn || body.containsBVar deBruijn.succ
  | app fn arg =>
    fn.containsBVar deBruijn || arg.containsBVar deBruijn
  | bvar deBruijnIndex =>
    deBruijnIndex == deBruijn
  | letE _ type value body _  =>
    type.containsBVar deBruijn || value.containsBVar deBruijn || body.containsBVar deBruijn.succ
  | fvar _ | sort _ | const .. | lit _ | mvar .. =>
    -- mvar possibly contains a deBruijn index, but it's difficult to check
    false
  | mdata _ expr
  | proj _ _ expr =>
    expr.containsBVar deBruijn
