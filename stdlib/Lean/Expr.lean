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
  | 0 =>
    list
  | n + 1 =>
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
  | e  =>
    panic! s!"Expected an operator of Eq, Iff, SEq, HEq, Ne, Gt, Lt, Ge, Le, And, Or, but got {e.ctorName} :\n{e}"

@[symm]
theorem LT.symm [LT α] {a b : α} (h : a < b) : b > a := h
@[symm]
theorem LE.symm [LE α] {a b : α} (h : a ≤ b) : b ≥ a := h
@[symm]
theorem GT.symm [LT α] {a b : α} (h : a > b) : b < a := h
@[symm]
theorem GE.symm [LE α] {a b : α} (h : a ≥ b) : b ≤ a := h

def Lean.Expr.symm : Expr → Expr
  | .app (.app (.app (.const `Eq us) α) a) b =>
    (Expr.const `Eq.symm us).mkApp [α, a, b]
  | .app (.app (.const `Iff us) a) b =>
    (Expr.const `Iff.symm us).mkApp [a, b]
  | .app (.app (.app (.app (.app (.app (.const `SEq us) α) Vector) n) m) a) b =>
    (Expr.const `SEq.symm us).mkApp [α, Vector, n, m, a, b]
  | .app (.app (.app (.app (.const `HEq us) α) a) β) b =>
    (Expr.const `HEq.symm us).mkApp [α, β, a, b]
  | .app (.app (.app (.const `Ne us) α) a) b =>
    (Expr.const `Ne.symm us).mkApp [α, a, b]
  | .app (.app (.app (.app (.const `LT.lt us) α) I) a) b =>
    (Expr.const `LT.symm us).mkApp [α, I, a, b]
  | .app (.app (.app (.app (.const `LE.le us) α) I) a) b =>
    (Expr.const `LE.symm us).mkApp [α, I, a, b]
  | .app (.app (.app (.app (.const `GT.gt us) α) I) a) b =>
    (Expr.const `GT.symm us).mkApp [α, I, a, b]
  | .app (.app (.app (.app (.const `GE.ge us) α) I) a) b =>
    (Expr.const `GE.symm us).mkApp [α, I, a, b]
  | .app (.app (.const `And us) a) b =>
    (Expr.const `And.symm us).mkApp [a, b]
  | .app (.app (.const `Or us) a) b =>
    (Expr.const `Or.symm us).mkApp [a, b]
  | .app (.app (.app (.app (.const `HasEquiv.Equiv us) α) self) a) b =>
    (Expr.const `Setoid.symm us).mkApp [α, self, a, b]
  | e  =>
    panic! s!"Expected an operator of Eq, Iff, SEq, HEq, Ne, Gt, Lt, Ge, Le, And, Or, but got {e.ctorName} :\n{e}"

def Lean.Expr.decomposeType : Expr → Expr × Expr
  | .app (.app (.app (.app (.const `letFun us) α) β) v) (.lam binderName binderType body binderInfo) =>
    let args := body.decomposeType
    ⟨
      (Expr.const `letFun us).mkApp [α, β, v, .lam binderName binderType args.fst binderInfo],
      .letE binderName binderType v args.snd false
    ⟩
  | .letE declName type value body nondep =>
    let fn := fun body => .letE declName type value body nondep
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

def Lean.Expr.getElem2get : Expr → Expr
  | app (app (app (app (app (app (app (app (const `GetElem.getElem _) coll) idx) _) _) _) xs) i) isLt =>
    match coll, idx with
    | app (app (const `List.Vector us) α) n, app (const `Fin usFin) n' =>
      let i :=
        if n == n' then
          i
        else
          (const `Fin.mk usFin).mkApp [n, (const `Fin.val usFin).mkApp [n', i], isLt]
      (const `List.Vector.get us).mkApp [α, n, xs, i]
    | app (const `List us) α, const `Nat usNat =>
      let i := (const `Fin.mk usNat).mkApp [(const `List.length us).mkApp [α, xs], i, isLt]
      (const `List.get us).mkApp [α, xs, i]
    | app (app (const `Tensor us) α) s, app (const `Fin _) _ =>
      (const `Tensor.get us).mkApp [α, s, xs, i]
    | _, _ =>
      panic! s!"Expected a collection, but got: coll = {coll}, idx = {idx}"
  | app fn arg =>
    app fn.getElem2get arg.getElem2get
  | forallE binderName binderType body binderInfo =>
    forallE binderName binderType.getElem2get body.getElem2get binderInfo
  | lam binderName binderType body binderInfo =>
    lam binderName binderType.getElem2get body.getElem2get binderInfo
  | letE declName type value body nondep =>
    letE declName (type.getElem2get) (value.getElem2get) (body.getElem2get) nondep
  | proj typeName idx struct => proj typeName idx struct.getElem2get
  | mdata data expr => mdata data expr.getElem2get
  | expr => expr

def Lean.Expr.fin2val : Expr → Expr
  | expr@(app (app (app (app (app (app (app (app (const `GetElem.getElem us) coll) idx) elem) _) self) xs) i) h) =>
    match idx, self with
    | app (const `Fin usFin) n, app (app (app _ valid) _) self =>
      let idx := const `Nat usFin
      let i := app (app (const `Fin.val usFin) n) i
      app (app (app (app (app (app (app (app (const `GetElem.getElem us) coll) idx) elem) valid) self) xs) i) h
    | _, _ =>
      expr
  | app fn arg =>
    app fn.fin2val arg.fin2val
  | forallE binderName binderType body binderInfo =>
    forallE binderName binderType.fin2val body.fin2val binderInfo
  | lam binderName binderType body binderInfo =>
    lam binderName binderType.fin2val body.fin2val binderInfo
  | letE declName type value body nondep =>
    letE declName (type.fin2val) (value.fin2val) (body.fin2val) nondep
  | proj typeName idx struct => proj typeName idx struct.fin2val
  | mdata data expr => mdata data expr.fin2val
  | expr => expr

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
