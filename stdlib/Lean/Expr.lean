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
  | .app (.const `Not usNot) p =>
    (Expr.const `Not usNot).mkApp [p.comm]
  | e  =>
    panic! s!"Expected an operator of Eq, Iff, SEq, HEq, Ne, Lt, Le, Gt, Ge, And, Or, Not, but got {e.ctorName} :\n{e}"

@[symm]
theorem LT.symm [LT α] {a b : α} (h : a < b) : b > a := h
@[symm]
theorem LE.symm [LE α] {a b : α} (h : a ≤ b) : b ≥ a := h
@[symm]
theorem GT.symm [LT α] {a b : α} (h : a > b) : b < a := h
@[symm]
theorem GE.symm [LE α] {a b : α} (h : a ≥ b) : b ≤ a := h

theorem Not.LT.symm [LT α] {a b : α} (h : ¬a < b) : ¬b > a := h
theorem Not.LE.symm [LE α] {a b : α} (h : ¬a ≤ b) : ¬b ≥ a := h
theorem Not.GT.symm [LT α] {a b : α} (h : ¬a > b) : ¬b < a := h
theorem Not.GE.symm [LE α] {a b : α} (h : ¬a ≥ b) : ¬b ≤ a := h

theorem Not.Iff.symm {a b : Prop} (h : ¬(a ↔ b)) : ¬(b ↔ a) := fun h' => h h'.symm
theorem Not.And.symm {a b : Prop} (h : ¬(a ∧ b)) : ¬(b ∧ a) := fun h' => h h'.symm
theorem Not.Or.symm {a b : Prop} (h : ¬(a ∨ b)) : ¬(b ∨ a) := fun h' => h h'.symm

def Lean.Expr.symm_args : Expr → Name × List Level × List Expr
  | .app (.app (.app (.const `Eq us) α) a) b =>
    ⟨`Eq, us, [α, a, b]⟩
  | .app (.app (.const `Iff us) a) b =>
    ⟨`Iff, us, [a, b]⟩
  | .app (.app (.app (.app (.app (.app (.const `SEq us) α) Vector) n) m) a) b =>
    ⟨`SEq, us, [α, Vector, n, m, a, b]⟩
  | .app (.app (.app (.app (.const `HEq us) α) a) β) b =>
    ⟨`HEq, us, [α, β, a, b]⟩
  | .app (.app (.app (.const `Ne us) α) a) b =>
    ⟨`Ne, us, [α, a, b]⟩
  | .app (.app (.app (.app (.const `LT.lt us) α) I) a) b =>
    ⟨`LT, us, [α, I, a, b]⟩
  | .app (.app (.app (.app (.const `LE.le us) α) I) a) b =>
    ⟨`LE, us, [α, I, a, b]⟩
  | .app (.app (.app (.app (.const `GT.gt us) α) I) a) b =>
    ⟨`GT, us, [α, I, a, b]⟩
  | .app (.app (.app (.app (.const `GE.ge us) α) I) a) b =>
    ⟨`GE, us, [α, I, a, b]⟩
  | .app (.app (.const `And us) a) b =>
    ⟨`And, us, [a, b]⟩
  | .app (.app (.const `Or us) a) b =>
    ⟨`Or, us, [a, b]⟩
  | .app (.app (.app (.app (.const `HasEquiv.Equiv us) α) I) a) b =>
    ⟨`XEq, us, [α, I, a, b]⟩
  | .app (.const `Not _) p =>
    let ⟨name, us, args⟩ := p.symm_args
    ⟨`Not ++ name, us, args⟩
  | e  =>
    panic! s!"Expected an operator of Eq, Iff, SEq, HEq, Ne, Lt, Le, Gt, Ge, And, Or, Not, but got {e.ctorName} :\n{e}"

def Lean.Expr.symm (e : Expr) : Expr :=
  let ⟨name, us, args⟩ := e.symm_args
  (Expr.const (name ++ `symm) us).mkApp args

def Lean.Expr.decompose (e : Expr) (type : Nat → Expr → Expr) (value : Expr → Expr) (deBruijn : Nat := 0) : Expr × Expr :=
  match e with
  | .app (.app (.app (.app (.const `letFun us) α) β) v) (.lam binderName binderType body binderInfo) =>
    let args := body.decompose type value deBruijn.succ
    ⟨
      (Expr.const `letFun us).mkApp [α, β, v, .lam binderName binderType args.fst binderInfo],
      .letE binderName binderType v args.snd false
    ⟩
  | .letE declName t v body nondep =>
    let fn := fun body => .letE declName t v body nondep
    (body.decompose type value deBruijn.succ).map fn fn
  | e  =>
    ⟨type deBruijn e, value e⟩

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
  | expr@(app (app (app (app (app (app (app (app (const `GetElem.getElem _) coll) idx) elem) _) _) xs) i) isLt) =>
    match coll with
    | app (app (const `List.Vector us) α) n =>
      match idx with
      | app (const `Fin usNat) n' =>
        let isomorphic :=
          if n == n' then
            true
          else
            match n, n' with
            | app (app (app (app (const `List.prod _) (const `Nat _)) _) _) s, app (app (app (app (const `List.prod _) (const `Nat _)) _) _) s' =>
              s == s'
            | app
                (app
                  (app (const `List.headD _)
                    (const `Nat _)
                  )
                  (app
                    (app
                      (app (const `List.cons _)
                        (const `Nat _)
                      )
                      n
                    )
                    _ -- tail
                  )
                )
                (app (app (app (const `OfNat.ofNat _) (const `Nat _)) (lit (.natVal _))) (.app (const `instOfNatNat _) (lit (.natVal _)))), _ =>
              n == n'
            | _, _ =>
              false
        let i :=
          if isomorphic then
            i
          else
            let i := (const `Fin.val usNat).mkApp [n', i]
            (const `Fin.mk usNat).mkApp [n, i, isLt]
        (const `List.Vector.get us).mkApp [α, n, xs.getElem2get, i]
      | const `Nat usNat =>
        let i :=
          match i, n with
          | (.app (.app (.app (const `OfNat.ofNat usOfNat) (const `Nat _)) (lit (.natVal i))) (.app (const `instOfNatNat _) (lit (.natVal _)))), .app (const `Nat.succ _) n_pred =>
            (const `OfNat.ofNat usOfNat).mkApp [
              app (const `Fin usNat) n,
              lit (.natVal i),
              (const `Fin.instOfNat usNat).mkApp [n, (const `Nat.instNeZeroSucc usNat).mkApp [n_pred], lit (.natVal i)]
            ]
          | _, _=>
            (const `Fin.mk usNat).mkApp [n, i, isLt]
        (const `List.Vector.get us).mkApp [α, n, xs.getElem2get, i]
      | _=>
        panic! s!"Expected a Fin index, but got: {idx}"
    | app (const `List us) α =>
      let args : Option (List Level × Expr) :=
        match idx with
        | app (const `Fin usNat) n =>
          (usNat, (const `Fin.val usNat).mkApp [n, i])
        | const `Nat usNat =>
          (usNat, i)
        | _ =>
          none
      if let some (usNat, i) := args then
        let i := (const `Fin.mk usNat).mkApp [(const `List.length us).mkApp [α, xs], i, isLt]
        (const `List.get us).mkApp [α, xs.getElem2get, i]
      else
        expr
    | app (app (const `Tensor us) α) s =>
      let n : Option Expr :=
        match idx with
        | app (const `Fin _) n =>
          match n with
          | app (app (app (const `List.get _) (const `Nat _)) _) -- s
              (app
                (app
                  (app (const `Fin.mk _)
                    (.app (.app (const `List.length _) (const `Nat _)) _)
                  )
                  zero
                ) _
              )
          | app
              (app
                (app
                  (app
                    (app (app
                      (app
                        (app (const `GetElem.getElem _)
                          (.app (const `List _) (const `Nat _))
                        )
                        (const `Nat _)
                      )
                      (const `Nat _)) _
                    )
                    (.app (const `List.instGetElemNatLtLength _) (const `Nat _))
                  ) _
                )
                zero
              ) _ =>
            if let app (app (app (const `OfNat.ofNat _) (const `Nat _)) (lit (.natVal 0))) (app (const `instOfNatNat _) (lit (.natVal 0))) := zero then
              n
            else
              panic! s!"unmatched zero, got {zero}"
          | app (app (app (const `Tensor.length _) _) _) xs' =>
            if xs == xs' then
              none
            else
              n
          | app (app (const `Slice.length _) _) _ =>
            n
          | _ =>
            match s with
            | app (app (const `Tensor.matmul_shape _) _) _ =>
              n
            | app (app (app (const `List.cons _) (const `Nat _)) n') _ =>
              if n == n' then
                none
              else
                n
            | .app (.app (const `List.tail _) (const `Nat _)) S =>
              if let .app (.app (.app (const `List.cons _) (const `Nat _)) _) (.app (.app (.app (const `List.cons _) (const `Nat _)) n') _) := S then
                if n == n' then
                  none
                else
                  n
              else if let .app (.app (.app (.app (const `Fin.val_lt_of_le _) (.app (.app (.app (const `Tensor.length _) _) s') _)) n') _) _ := isLt then
                if s == s' && n == n' then
                  none
                else
                  n
              else
                n
            | .app (.app (.app (const `List.eraseIdx _) (const `Nat _)) (.app (.app (.app (const `List.cons _) (const `Nat _)) n') _)) (.app (.app (.app (const `OfNat.ofNat _) (const `Nat _)) (.lit (.natVal index))) (.app (const `instOfNatNat _) _)) =>
              if index > 0 && n == n' then
                none
              else
                n
            | _ =>
              if let .app (.app (.app (.app (const `Fin.val_lt_of_le _) (.app (.app (.app (const `Tensor.length _) _) s') (.app (.app (.app (const `Tensor.T _) _) (.app (.app (.app (const `List.cons _) (const `Nat _)) _) (.app (.app (.app (const `List.cons _) (const `Nat _)) n') _))) _))) n'') _) _ := isLt then
                if s == s' && n == n' && n == n'' then
                  none
                else
                  n
              else
                n
        | const `Nat _ =>
          some default
        | _ =>
          panic! s!"Expected a Fin index, but got: {idx}"
      let i :=
        if let some n := n then
          let i :=
            if n == default then
              i
            else
              (const `Fin.val []).mkApp [n, i]
          let n := (const `Tensor.length us).mkApp [α, s, xs]
          (const `Fin.mk []).mkApp [n, i, isLt]
        else
          i
      (const `Tensor.get us).mkApp [α, s, xs.getElem2get, i]
    | app (lam _ _ (app (app (const `List.Vector us) α) n) .default) deBruijn_0 =>
      -- (fun s => List.Vector α (fn s) n) s
      -- change # 0 to deBruijn_0
      let map := fun deBruijnIndex offset => if deBruijnIndex == offset then deBruijn_0.incDeBruijnIndex offset else if deBruijnIndex > offset then bvar (deBruijnIndex - 1) else bvar deBruijnIndex
      let α := α.mapDeBruijnIndex map 0
      let n := n.mapDeBruijnIndex map 0
      (const `List.Vector.get us).mkApp [α, n, xs.getElem2get, i]
    | app (app (lam _ _ (app (const `List.Vector us) _) .default) _) m'
      -- curried congrArg₂: outer binder `ℕ` or `List ℕ`; body is partial `List.Vector …`
    | app (app (lam _ _ (lam _ (const `Nat _) (app (app (const `List.Vector us) _) (bvar 0)) .default) .default) _) m' =>
      -- congrArg₂ (fun n m => …) / (fun s m => …): inner `ℕ` length + `List.Vector … (bvar 0)`
      let i :=
        if let (app (const `Fin usFin) m) := idx then
          if m == m' then
            i
          else
            let i := (const `Fin.val usFin).mkApp [m, i]
            (const `Fin.mk usFin).mkApp [m', i, isLt]
        else
          (const `Fin.mk []).mkApp [m', i, isLt]
      (const `List.Vector.get us).mkApp [elem, m', xs.getElem2get, i]
    | _ =>
      panic! s!"Expected a collection, but got: coll = {coll}"
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
  | expr@(app (app (app (app (app (app (app (app (const `GetElem.getElem us) coll) idx) elem) _) self) xs) i) isLt) =>
    match idx, self with
    | app (const `Fin usNat) n, app (app (app _ valid) _) self =>
      let idx := const `Nat usNat
      let i := app (app (const `Fin.val usNat) n) i
      app (app (app (app (app (app (app (app (const `GetElem.getElem us) coll) idx) elem) valid) self) xs.fin2val) i) isLt
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

def Lean.Expr.ofNatLit? (e : Expr) (lit : Nat := 1) : Option (Expr × Expr) :=
  match e with
  | .app (.app (.app (.const `OfNat.ofNat _) α) (.lit (.natVal k))) inst =>
    if k == lit then some (α, inst) else none
  | _ =>
    none

def Lean.Expr.asHMul? (e : Expr) : Option (Expr × Expr) :=
  let fn := e.getAppFn
  if fn.constName? != some `HMul.hMul && fn.constName? != some `Nat.mul then
    none
  else
    let args := e.getAppArgs
    if args.size < 2 then
      none
    else
      some (args[args.size - 2]!, args[args.size - 1]!)

def Lean.Expr.isOfNatLitUsedAsHMulLeft (root target : Expr) (lit : Nat) : Bool :=
  if target.ofNatLit? lit |>.isNone then
    false
  else
    match root.asHMul? with
    | some (left, _) =>
      left == target
    | none =>
      match root with
      | .app fn arg =>
        isOfNatLitUsedAsHMulLeft fn target lit || isOfNatLitUsedAsHMulLeft arg target lit
      | _ =>
        false

partial def Lean.Expr.replaceOfNatLitAsHMulLefts (e : Expr) (lit : Nat) (replacement : Expr) : Expr :=
  match e.asHMul? with
  | some (left, right) =>
    let left' :=
      if (left.ofNatLit? lit).isSome then replacement else replaceOfNatLitAsHMulLefts left lit replacement
    let right' := replaceOfNatLitAsHMulLefts right lit replacement
    let fn := e.getAppFn
    let args := e.getAppArgs
    if args.size >= 2 then
      mkAppN fn (args.take (args.size - 2) |>.push left' |>.push right')
    else
      e
  | none =>
    match e with
    | .app fn arg => .app (replaceOfNatLitAsHMulLefts fn lit replacement) (replaceOfNatLitAsHMulLefts arg lit replacement)
    | .forallE n t b i => .forallE n (replaceOfNatLitAsHMulLefts t lit replacement) (replaceOfNatLitAsHMulLefts b lit replacement) i
    | .lam n t b i => .lam n (replaceOfNatLitAsHMulLefts t lit replacement) (replaceOfNatLitAsHMulLefts b lit replacement) i
    | .letE n t v b nd => .letE n (replaceOfNatLitAsHMulLefts t lit replacement) (replaceOfNatLitAsHMulLefts v lit replacement) (replaceOfNatLitAsHMulLefts b lit replacement) nd
    | .mdata d expr => .mdata d (replaceOfNatLitAsHMulLefts expr lit replacement)
    | .proj s i expr => .proj s i (replaceOfNatLitAsHMulLefts expr lit replacement)
    | e => e

def Lean.Expr.replaceOfNatLitInConstArg (e : Expr) (lit : Nat) (constName : Name) (replacement : Expr) (argIdxFromEnd : Nat := 1) : Expr :=
  let rec go (e : Expr) : Expr :=
    if e.getAppFn.constName? == some constName then
      let args := e.getAppArgs
      if argIdxFromEnd ≤ args.size then
        let idx := args.size - argIdxFromEnd
        if (args[idx]!.ofNatLit? lit).isSome then
          mkAppN e.getAppFn (args.take idx |>.push replacement |>.append (args.drop (idx + 1)))
        else
          match e with
          | .app fn arg => .app (go fn) (go arg)
          | .forallE n t b i => .forallE n (go t) (go b) i
          | .lam n t b i => .lam n (go t) (go b) i
          | .letE n t v b nd => .letE n (go t) (go v) (go b) nd
          | .mdata d expr => .mdata d (go expr)
          | .proj s i expr => .proj s i (go expr)
          | e => e
      else
        match e with
        | .app fn arg => .app (go fn) (go arg)
        | .forallE n t b i => .forallE n (go t) (go b) i
        | .lam n t b i => .lam n (go t) (go b) i
        | .letE n t v b nd => .letE n (go t) (go v) (go b) nd
        | .mdata d expr => .mdata d (go expr)
        | .proj s i expr => .proj s i (go expr)
        | e => e
    else
      match e with
      | .app fn arg => .app (go fn) (go arg)
      | .forallE n t b i => .forallE n (go t) (go b) i
      | .lam n t b i => .lam n (go t) (go b) i
      | .letE n t v b nd => .letE n (go t) (go v) (go b) nd
      | .mdata d expr => .mdata d (go expr)
      | .proj s i expr => .proj s i (go expr)
      | e => e
  go e

def Lean.Expr.findOfNatLitInConstArg (e : Expr) (lit : Nat) (constName : Name) (argIdxFromEnd : Nat := 1) : Option (Expr × Expr × Expr) :=
  let rec go (e : Expr) : Option (Expr × Expr × Expr) :=
    if e.getAppFn.constName? == some constName then
      let args := e.getAppArgs
      if argIdxFromEnd ≤ args.size then
        let arg := args[args.size - argIdxFromEnd]!
        match arg.ofNatLit? lit with
        | some (α, inst) => some (α, inst, arg)
        | none => none
      else
        none
    else
      match e with
      | .app fn arg => go fn <|> go arg
      | .forallE _ binderType body _ => go binderType <|> go body
      | .lam _ binderType body _ => go binderType <|> go body
      | .letE _ type value body _ => go type <|> go value <|> go body
      | .mdata _ expr
      | .proj _ _ expr =>
        go expr
      | _ =>
        none
  go e

def Lean.Expr.isOfNatLitRepeatCount (root target : Expr) (lit : Nat) : Bool :=
  if target.ofNatLit? lit |>.isNone then
    false
  else
    match root.getAppFn.constName? with
    | some `List.Vector.repeat =>
      let args := root.getAppArgs
      args.size >= 2 && (args[args.size - 1]!.ofNatLit? lit).isSome
    | some `Tensor.repeat =>
      let args := root.getAppArgs
      args.size >= 3 && (args[args.size - 1]!.ofNatLit? lit).isSome
    | _ =>
      match root with
      | .app fn arg =>
        isOfNatLitRepeatCount fn target lit || isOfNatLitRepeatCount arg target lit
      | _ =>
        false

def Lean.Expr.collectOfNatLit (e : Expr) (lit : Nat := 1) : List (Expr × Expr × Expr) :=
  let here := match e.ofNatLit? lit with | some (α, inst) => [(α, inst, e)] | none => []
  match e with
  | .app fn arg =>
    collectOfNatLit fn lit ++ collectOfNatLit arg lit ++ here
  | .forallE _ binderType body _ =>
    collectOfNatLit binderType lit ++ collectOfNatLit body lit ++ here
  | .lam _ binderType body _ =>
    collectOfNatLit binderType lit ++ collectOfNatLit body lit ++ here
  | .letE _ type value body _ =>
    collectOfNatLit type lit ++ collectOfNatLit value lit ++ collectOfNatLit body lit ++ here
  | .mdata _ expr
  | .proj _ _ expr =>
    collectOfNatLit expr lit ++ here
  | _ =>
    here

def Lean.Expr.findOfNatLit (e : Expr) (lit : Nat := 1) : Option (Expr × Expr × Expr) :=
  let found := e.collectOfNatLit lit
  if lit == 1 then
    match e.findOfNatLitInConstArg lit `List.Vector.repeat <|> e.findOfNatLitInConstArg lit `Tensor.repeat with
    | some result => some result
    | none =>
      match found.find? fun ⟨_, _, target⟩ => e.isOfNatLitRepeatCount target lit with
      | some result => some result
      | none =>
        match found.find? fun ⟨_, _, target⟩ => !e.isOfNatLitUsedAsHMulLeft target lit with
        | some result => some result
        | none => found[0]?
  else
    found[0]?

def Lean.Expr.mkOfNatLit (α inst : Expr) (lit : Nat := 1) : Expr :=
  (.app (.app (.app (.const `OfNat.ofNat []) α) (.lit (.natVal lit))) inst)

def Lean.Expr.mapOfNatLit (e : Expr) (lit : Nat) (nIdx : Nat) : Expr × Nat :=
  match e.ofNatLit? lit with
  | some _ =>
    (.bvar nIdx, 1)
  | none =>
    match e with
    | .app fn arg =>
      let ⟨fn', n₁⟩ := mapOfNatLit fn lit nIdx
      let ⟨arg', n₂⟩ := mapOfNatLit arg lit nIdx
      (.app fn' arg', n₁ + n₂)
    | .forallE binderName binderType body binderInfo =>
      let ⟨binderType', n₁⟩ := mapOfNatLit binderType lit nIdx
      let ⟨body', n₂⟩ := mapOfNatLit body lit nIdx.succ
      (.forallE binderName binderType' body' binderInfo, n₁ + n₂)
    | .lam binderName binderType body binderInfo =>
      let ⟨binderType', n₁⟩ := mapOfNatLit binderType lit nIdx
      let ⟨body', n₂⟩ := mapOfNatLit body lit nIdx.succ
      (.lam binderName binderType' body' binderInfo, n₁ + n₂)
    | .letE declName type value body nondep =>
      let ⟨type', n₁⟩ := mapOfNatLit type lit nIdx
      let ⟨value', n₂⟩ := mapOfNatLit value lit nIdx
      let ⟨body', n₃⟩ := mapOfNatLit body lit nIdx.succ
      (.letE declName type' value' body' nondep, n₁ + n₂ + n₃)
    | .mdata data expr =>
      let ⟨expr', n⟩ := mapOfNatLit expr lit nIdx
      (.mdata data expr', n)
    | .proj typeName idx struct =>
      let ⟨struct', n⟩ := mapOfNatLit struct lit nIdx
      (.proj typeName idx struct', n)
    | expr =>
      (expr, 0)

def Lean.Expr.oneBinderInsertPos (oneType : Expr) : Nat :=
  match oneType with
  | .const `Nat _ => 0
  | .bvar k => k
  | _ => 0

def Lean.Expr.replaceExpr (e replacement target : Expr) : Expr × Bool :=
  if e == target then (replacement, true) else
  match e with
  | .app fn arg =>
    let (fn', found) := fn.replaceExpr replacement target
    if found then (.app fn' arg, true) else
      let (arg', found) := arg.replaceExpr replacement target
      (.app fn arg', found)
  | .lam n t b i =>
    let (t', found) := t.replaceExpr replacement target
    if found then (.lam n t' b i, true) else
      let (b', found) := b.replaceExpr replacement target
      (.lam n t b' i, found)
  | .forallE n t b i =>
    let (t', found) := t.replaceExpr replacement target
    if found then (.forallE n t' b i, true) else
      let (b', found) := b.replaceExpr replacement target
      (.forallE n t b' i, found)
  | .letE n t v b nd =>
    let (t', found) := t.replaceExpr replacement target
    if found then (.letE n t' v b nd, true) else
      let (v', found) := v.replaceExpr replacement target
      if found then (.letE n t v' b nd, true) else
        let (b', found) := b.replaceExpr replacement target
        (.letE n t v b' nd, found)
  | .mdata d e =>
    let (e', found) := e.replaceExpr replacement target
    (.mdata d e', found)
  | .proj s i e =>
    let (e', found) := e.replaceExpr replacement target
    (.proj s i e', found)
  | _ => (e, false)

def Lean.Expr.isNumericType (e : Expr) : Bool :=
  match e with
  | .const `Nat _ | .const `Int _ => true
  | _ => false

def Lean.Expr.replaceAllExpr (e replacement target : Expr) : Expr :=
  if e == target then replacement else
  match e with
  | .app fn arg =>
    .app (fn.replaceAllExpr replacement target) (arg.replaceAllExpr replacement target)
  | .lam n t b i =>
    .lam n (t.replaceAllExpr replacement target) (b.replaceAllExpr replacement target) i
  | .forallE n t b i =>
    .forallE n (t.replaceAllExpr replacement target) (b.replaceAllExpr replacement target) i
  | .letE n t v b nd =>
    .letE n (t.replaceAllExpr replacement target) (v.replaceAllExpr replacement target) (b.replaceAllExpr replacement target) nd
  | .mdata d e =>
    .mdata d (e.replaceAllExpr replacement target)
  | .proj s i e =>
    .proj s i (e.replaceAllExpr replacement target)
  | _ => e

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
