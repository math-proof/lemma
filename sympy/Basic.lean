import Mathlib.Tactic
import stdlib.Lean.Syntax
import stdlib.Lean.Environment
import stdlib.Lean.Expr
open Lean
open Lean.Meta

/--
Registers a custom attribute `@[main]` that, when applied to a theorem or definition,
creates a new declaration whose name reflects the source file path and the original name.

- The new name is constructed by:
  1. Removing the main module name from the path.
  2. Appending a lowercased suffix of the original declaration name.
  3. Omitting the suffix if it is `main`.

This is useful for automatically generating namespaced lemmas from file structure,
helpful in large-scale automated lemma generation systems.

Example:
If `MyLib.Group.Basic` contains `def Main`, the resulting name will be `Group.Basic`.
If it contains `def LeftId`, the resulting name will be `Group.Basic.leftid`.

Usage:
```lean
@[main]
lemma MyLemma : ...
```
-/
initialize registerBuiltinAttribute {
  name := `main
  descr := "An attribute that creates a file-path-based alias for a lemma declaration"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    addDecl <| .defnDecl {
      name := (← getEnv).module.lemmaName declName
      levelParams := levelParams
      type := decl.type
      value := .const declName (levelParams.map .param)
      hints := .abbrev
      safety := .safe
    }
}

/--
Helper functions for parsing and transforming declaration names based on infix operators. example:
["Expr", "eq", "Expr", "Expr", "Expr", "lt", "Expr"].parseInfixSegments = [["Expr", "eq", "Expr"], ["Expr"], ["Expr", "lt", "Expr"]]
-/
def List.parseInfixSegments (list : List String) : List (List String) :=
  match _: list with
  | [] => []
  | [x] => [[x]]
  | x :: op :: y =>
    match op with
    | "eq" | "is" | "as" | "ne" | "lt" | "le" | "gt" | "ge" | "in" | "ou" | "et" =>
      list.take 3 :: parseInfixSegments (y.drop 1)
    | _ =>
      [x] :: parseInfixSegments (op :: y)
termination_by list.length

def List.transformPrefix (list : List String) : List String :=
  if list.length == 1 then
    [list.head!.transformPrefix]
  else
    match list[1]! with
    | "eq" | "is" | "as" | "ne" =>
      list.reverse
    | _ =>
      list

def List.decomposeOf (list : List String) (parity : List Bool) (map : List String → List String) (offset : ℕ := 0) : List String :=
  if let some i := list.idxOf? "of" then
    let ⟨first, ofPart⟩ := list.splitAt i
    let ofPart :=
      if offset == 0 then
        ofPart[0]! :: (ofPart.tail.parseInfixSegments.zipWith (fun s b => if b then s.transformPrefix else s) parity).flatten
      else
        ofPart.drop offset
    first.head! :: map first.tail ++ ofPart
  else
    list.head! :: map list.tail

def List.commutateIs (list : List String) (op : String := "is") : List String :=
  if let some i := list.idxOf? "is" then
    let ⟨first, second⟩ := list.splitAt i
    second.tail ++ op :: first
  else
    []

def List.comm (list : List String) (parity : List Bool) : List String :=
  list.decomposeOf parity fun list =>
    let list' := list.commutateIs
    if list'.isEmpty then
      if let first :: rest := list then
        if let op :: second :: rest := rest then
          match op with
          | "eq" | "as" | "ne" | "le" | "ge" | "lt" | "gt" =>
            [second, op, first] ++ rest
          | _ =>
            panic! s!"Expected the operator 'eq', 'as or 'ne', got: {op}"
        else
          [first.transformPrefix] ++ rest
      else
        panic! s!"Declaration does not have the form `... eq/is/as/ne ...`, got: {list}"
    else
      list'

def List.zipParity (binders : List (Name × Expr × BinderInfo)) (parity : ℕ) (info : BinderInfo := .default) : List (Bool × Name × Expr × BinderInfo) :=
  binders.foldr
    (fun binder@⟨_, _, binderInfo⟩ ⟨binders, parity⟩ =>
      let ⟨bit, parity⟩ :=
        if binderInfo == info then
          (parity % 2 == 1, parity / 2)
        else
          (false, parity)
      ⟨⟨bit, binder⟩ :: binders, parity⟩
    )
    ([], parity)
  |> Prod.fst

def List.extractParity (parity : List (Bool × Expr)) : CoreM (List String × List Bool) := do
  let moduleTokens := (← getEnv).moduleTokens
  let i := moduleTokens.idxOf "of"
  let ofPart := (moduleTokens.splitAt i).snd.tail
  let parity ←
    if parity.length > ofPart.length && ofPart.length > 0 then
      parity.filterMapM fun ⟨comm, type⟩ => do
        try
          if ← MetaM.run' type.is_Prop then
            return some comm
          else
            return none
        catch _ =>
          return none
    else
      pure (parity.map fun ⟨comm, _⟩ => comm)
  return ⟨moduleTokens, parity⟩

def Expr.comm (type proof : Expr) (parity : ℕ := 0) : List (Bool × Expr) × Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let binders := binders.zipParity parity
  let ⟨type, symm⟩ := type.decomposeType
  let telescope := fun localBinders lam body =>
    binders.foldl
      (fun body ⟨comm, binderName, binderType, binderInfo⟩ => lam binderName (if comm then binderType.comm else binderType) body binderInfo)
      (localBinders.foldl
        (fun body ⟨declName, type, deBruijn⟩ =>
          let type := type.incDeBruijnIndex (deBruijn + 1)
          .letE declName type (.app type.comm.symm (.bvar deBruijn)) ((body.incDeBruijnIndex 1).setDeBruijnIndex (deBruijn + 1) 0) false
        )
        body
      )
  let valueBinders := binders.zipIdx.filterMap fun ⟨⟨comm, binderName, binderType, _⟩, deBruijn⟩ => if comm then some (binderName, binderType, deBruijn) else none
  (
    binders.filterMap fun ⟨comm, _, binderType, binderInfo⟩ => if binderInfo == .default then some ⟨comm, binderType⟩ else none,
    (type, .app symm (proof.mkApp ((List.range binders.length).map fun i => .bvar i).reverse)).map
      (telescope (valueBinders.filterMap fun args@⟨_, _, deBruijn⟩ => if type.containsBVar deBruijn then some args else none) Expr.forallE)
      (telescope valueBinders .lam)
  )

/--
`@[comm]` (abbreviated from `law of commutativity` : 交换律) attribute automatically generates the symmetric version of a theorem
if it proves an equality.

Usage:
```lean
@[comm]
theorem Section.LHS.eq.RHS {c : γ} (a : α) (b : β) : lhs a b = rhs a b:= by proof
-- Generates:
theorem Section.RHS.eq.LHS {c : γ} (a : α) (b : β) : rhs a b = lhs a b := (Section.LHS.eq.RHS a b).symm

@[comm 6]
theorem Section.LHS.eq.RHS.of.Eq.Eq.Eq (h₀ : α = α') (h₁ : β = β') (h₂ : γ = γ'): lhs h₀ h₁ h₂ = rhs h₀ h₁ h₂ := by proof
-- 6 is decomposed as binary digits : 110 => [0, 1, 1], where each bit represents whether the corresponding default binder is commutated or not.
Generates:
theorem Section.RHS.eq.LHS.of.Eq.Eq.Eq (h₀ : α' = α) (h₁ : β' = β) (h₂ : γ = γ'): lhs h₀.symm h₁.symm h₂ = rhs h₀.symm h₁.symm h₂ := (Section.LHS.eq.RHS.of.Eq.Eq.Eq h₀.symm h₁.symm h₂).symm
```
-/
initialize registerBuiltinAttribute {
  name := `comm
  descr := "Automatically generate the commutative version of an equality theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨parity, type, value⟩ := Expr.comm decl.type (.const declName (levelParams.map .param)) stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((moduleTokens.comm parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.mp (type proof : Expr) (parity : ℕ := 0) (reverse : Bool := false) (and : Bool := false) : ℕ × Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let deBruijn := (binders.zipParity parity .instImplicit).zipIdx.filterMap fun ⟨⟨bit, _⟩, deBruijn⟩ => if bit then some deBruijn else none
  let decDeBruijnIndex := fun type => deBruijn.foldr (fun deBruijn type => type.decDeBruijnIndex 1 deBruijn) type
  let type := decDeBruijnIndex type
  let binders := deBruijn.foldr
    (fun deBruijn binders =>
      let ⟨lowerPart, higherPart⟩ := binders.splitAt deBruijn
      let lowerPart := lowerPart.map fun ⟨binderName, binderType, binderInfo⟩ => ⟨binderName, binderType.decDeBruijnIndex 1, binderInfo⟩
      lowerPart ++ higherPart.tail
    )
    binders
  let ⟨us, lhs, rhs⟩ := type.decomposeIff
  let ⟨given, imply, mp⟩ := if reverse then (rhs, lhs.incDeBruijnIndex 1, `Iff.mpr) else (lhs, rhs.incDeBruijnIndex 1, `Iff.mp)
  let binders : List (Name × Expr × BinderInfo) := binders.zipIdx.map fun ⟨⟨binderName, binderType, binderInfo⟩, deBruijn⟩ =>
    (binderName, binderType, (if binderInfo == .default && given.containsBVar deBruijn then .implicit else binderInfo))
  let telescope := fun lam body =>
    binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
  let proof :=
    if parity > 0 then
      let ⟨_, intro⟩ := proof.decompose_lam []
      let ⟨_, mp, mpr⟩ := intro.decomposeIff
      let mp := if reverse then mpr else mp
      decDeBruijnIndex mp
    else
      (Expr.const mp us).mkApp [lhs, rhs, proof.mkApp ((List.range binders.length).map fun i => .bvar i).reverse]
  let ⟨h_curr, h_next⟩ := if and then ⟨[given], []⟩ else given.decomposeAnd
  let h_name := (List.range h_curr.length).map fun i => .str default ("h" ++ i.toSubscriptString)
  let pNameType := h_name.zip h_curr
  let ⟨h₀, h₀Type⟩ := pNameType.head!
  let pNameType := pNameType.tail
  let size := h_curr.length
  let deBruijn := (List.range size).drop 1
  let bvar := (deBruijn.reverse.zip (h_curr.zip h_next)).foldr
    (fun ⟨deBruijn, h_curr, h_next⟩ bvar =>
      (Expr.const `And.intro us).mkApp [
        h_curr.incDeBruijnIndex size,
        h_next.incDeBruijnIndex size,
        .bvar deBruijn,
        bvar
      ]
    )
    (.bvar 0)
  let imply := pNameType.foldr (fun ⟨name, type⟩ imply => (Expr.forallE name type imply .default).incDeBruijnIndex 1) imply
  let proof := Expr.app (proof.incDeBruijnIndex size) bvar
  let proof := (deBruijn.zip pNameType).foldr (fun ⟨deBruijn, name, type⟩ proof => (.lam name (type.incDeBruijnIndex deBruijn) proof .default)) proof
  (
    binders.countP (·.snd.snd == .default),
    (.forallE h₀ h₀Type imply .default, .lam h₀ h₀Type proof .default).map (telescope Expr.forallE) (telescope .lam)
  )

def List.mp (list : List String) : List String := list.decomposeOf [] (fun list => list.commutateIs "of") 1
def List.comm.is (list : List String) (parity : List Bool) : List String :=
  list.decomposeOf parity fun list =>
    let i := list.idxOf "is"
    let ⟨lhs, rhs⟩ := list.splitAt i
    let lhs := lhs.transformPrefix
    let rhs := rhs.tail.transformPrefix
    lhs ++ "is" :: rhs

/--
`@[mp]` (abbreviated from `modus ponens`) attribute automatically generates the mp implication of a equivalence theorem.
Usage:
```lean
@[mp]
theorem Section.LHS.is.RHS {c : γ} (a : α) (b : β) : lhs a b ↔ rhs a b:= ⟨proof.mp, proof.mpr⟩
-- Generates:
theorem Section.RHS.of.LHS {c : γ} {a : α} {b : β} (h : lhs a b): rhs a b := (Section.LHS.eq.RHS a b).mp h

@[mp 4]
theorem Section.LHS.is.RHS [Class_0 α] [Class_1 α] [Class_2 α] {c : γ} (a : α) (b : β) : lhs a b ↔ rhs a b:= by proof
-- 4 is decomposed as binary digits : 100 => [0, 0, 1], where each bit represents whether the corresponding instImplicit binder is filtered.
Generates:
theorem Section.RHS.of.LHS [Class_0 α] [Class_1 α] {c : γ} {a : α} {b : β} (h : lhs a b): rhs a b := proof.mp h
```
notice that the default dependent arguments (a : α) (b : β) are made implicit {a : α} {b : β}
-/
initialize registerBuiltinAttribute {
  name := `mp
  descr := "Automatically generate the mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨_, type, value⟩ := Expr.mp decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity (and := stx.getIdent == `and)
    addAndCompile <| .thmDecl {
      name := ((← getEnv).moduleTokens.mp.foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.mpr (type proof : Expr) (parity : ℕ := 0) (and : Bool := false) : ℕ × Expr × Expr := Expr.mp type proof parity true and
def List.mpr (list : List String) : List String :=
  list.decomposeOf []
    (fun list =>
      let i := list.idxOf "is"
      let ⟨first, second⟩ := list.splitAt i
      first ++ "of" :: second.tail
    ) 1

/--
`@[mpr]` (abbreviated from `modus ponens reverse`) attribute automatically generates the mpr implication of a equivalence theorem.
Usage:
```lean
@[mpr]
theorem Section.LHS.is.RHS {c : γ} (a : α) (b : β) : lhs a b ↔ rhs a b:= by proof
-- Generates:
theorem Section.LHS.of.RHS {c : γ} {a : α} {b : β} (h : rhs a b) : lhs a b := (Section.LHS.eq.RHS a b).mpr h
```
-/
initialize registerBuiltinAttribute {
  name := `mpr
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨_, type, value⟩ := Expr.mpr decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity (stx.getIdent == `and)
    addAndCompile <| .thmDecl {
      name := ((← getEnv).moduleTokens.mpr.foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mp.comm]` attribute automatically generates the commutative mp implication of a equivalence theorem.
Usage:
```lean
@[mpr]
theorem Section.LHS.is.RHS {c : γ} (a : α) (b : β) : lhs a b ↔ a = b:= by proof
-- Generates:
theorem Section.RHS'.of.LHS {c : γ} {a : α} {b : β} (h : lhs a b) : b = a := (Section.LHS.eq.RHS a b).mp.symm
```
-/
initialize registerBuiltinAttribute {
  name := `mp.comm
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨n, type, value⟩ := Expr.mp decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity (and := stx.getIdent == `and)
    -- 2ⁿ, where n is the number of default binders
    let ⟨parity, type, value⟩ := Expr.comm type value (1 <<< n)
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((moduleTokens.mp.comm parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

/--
`@[mpr.comm]` attribute automatically generates the commutative mpr implication of a equivalence theorem.
Usage:
```lean
@[mpr]
theorem Section.LHS.is.RHS {c : γ} (a : α) (b : β) : a = b ↔ rhs a b:= by proof
-- Generates:
theorem Section.LHS'.of.RHS {c : γ} {a : α} {b : β} (h : rhs a b) : b = a := (Section.LHS.eq.RHS a b).mpr.symm
```
-/
initialize registerBuiltinAttribute {
  name := `mpr.comm
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let ⟨n, type, value⟩ := Expr.mpr decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity (stx.getIdent == `and)
    let ⟨parity, type, value⟩ := Expr.comm type value (1 <<< n)
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((moduleTokens.mpr.comm parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.comm.is (type mp mpr : Lean.Expr) (parity : ℕ := 0) : List (Bool × Expr) × Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let args := ((List.range binders.length).map fun i => .bvar i).reverse
  let binders := binders.zipParity parity
  let mp := mp.mkApp args
  let mpr := mpr.mkApp args
  let ⟨us, lhs, rhs⟩ := type.decomposeIff
  let lhs := lhs.comm
  let rhs := rhs.comm
  let telescope := fun localBinders lam body =>
    binders.foldl
      (fun body ⟨comm, binderName, binderType, binderInfo⟩ => lam binderName (if comm then binderType.comm else binderType) body binderInfo)
      (localBinders.foldl
        (fun body ⟨declName, type, deBruijn⟩ =>
          let type := type.incDeBruijnIndex (deBruijn + 1)
          .letE declName type (.app type.comm.symm (.bvar deBruijn)) ((body.incDeBruijnIndex 1).setDeBruijnIndex (deBruijn + 1) 0) false
        )
        body
      )
  let valueBinders := binders.zipIdx.filterMap fun ⟨⟨comm, binderName, binderType, _⟩, deBruijn⟩ => if comm then some (binderName, binderType, deBruijn) else none
  (
    binders.filterMap fun ⟨comm, _, binderType, binderInfo⟩ => if binderInfo == .default then some ⟨comm, binderType⟩ else none,
    ((Expr.const `Iff us).mkApp [lhs, rhs], (Expr.const `Iff.intro us).mkApp [lhs, rhs, mp, mpr]).map
      (telescope (valueBinders.filterMap fun args@⟨_, _, deBruijn⟩ => if type.containsBVar deBruijn then some args else none) Expr.forallE)
      (telescope valueBinders .lam)
  )

/--
`@[comm.is]` attribute automatically generates the commutative version of an equivalence (Iff) theorem.
Usage:
```lean
@[mpr]
theorem Section.LHS.is.RHS (a : α) (b : β) : a ≃ b ↔ a' = b':= by proof
-- Generates:
theorem Section.LHS'.is.RHS' {a : α} {b : β} : b ≃ a ↔ b' = a':= ⟨mr.comm, mpr.comm⟩
```
-/
initialize registerBuiltinAttribute {
  name := `comm.is
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams

    let proof := .const declName (levelParams.map .param)
    let ⟨n, type, value⟩ := Expr.mpr decl.type proof (and := true)
    let ⟨_, type, mpr⟩ := Expr.comm type value (1 <<< n)

    let ⟨n, type, value⟩ := Expr.mp decl.type proof (and := true)
    let ⟨_, type, mp⟩ := Expr.comm type value (1 <<< n)

    let ⟨parity, type, value⟩ := Expr.comm.is decl.type mp mpr stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((List.comm.is moduleTokens parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def List.Not (list : List String) : List String :=
  if list.length == 1 then
    [list.head!.Not]
  else
    let op :=
      match list[1]! with
      | "eq"  => "ne"
      | "ne" => "eq"
      | _ =>
        panic! s!"Expected the operator 'eq' or 'ne', got: {list[1]!}"
    list[0]! :: op :: list.tail

def List.mt (list : List String) : Name :=
  let i := list.idxOf "of"
  let ⟨first, ofPart⟩ := list.splitAt i
  let domain := first[0]!
  let first := first.tail
  let of := ofPart[0]!
  let ofPart := ofPart.tail.parseInfixSegments
  let (first, ofPart) := (ofPart[0]!, ofPart.set 0 first.Not)
  (domain :: first.Not ++ of :: ofPart.map (".".intercalate ·)).foldl Name.str default

def Expr.mt (type proof : Lean.Expr) : Lean.Expr × Lean.Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let b := type
  let Not := fun type =>
    match type with
    | .app (.const `Not _) arg =>
      arg
    | .app (.app (.const `Eq us) lhs) rhs =>
      (Lean.Expr.const `Ne us).mkApp [lhs, rhs]
    | .app (.app (.const `Ne us) lhs) rhs =>
      (Lean.Expr.const `Eq us).mkApp [lhs, rhs]
    | _ =>
      (Lean.Expr.const `Not []).mkApp [type]
  let h :=
    let h := Lean.Expr.bvar 0
    match type with
    | .app (.const `Not _) arg =>
      (Lean.Expr.const `Iff.mpr []).mkApp [
        (Lean.Expr.const `Not []).mkApp [(Lean.Expr.const `Not []).mkApp [arg]],
        arg,
        (Lean.Expr.const `Classical.not_not []).mkApp [arg],
        h
      ]
    | _ =>
      h
  let (binders, type, a) :=
    if let ⟨h, premise, .default⟩ :: rest := binders then
      let a := premise.incDeBruijnIndex 1
      ((h, Not (type.decDeBruijnIndex 1), BinderInfo.default) :: rest, Not a, a)
    else
      panic! "The theorem must have at least one hypothesis."
  let telescope := fun lam body =>
    binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
  -- mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a
  let proof := ((Lean.Expr.const `mt []).mkApp [a, b, proof.mkApp [(.bvar 1)], h])
  (type, proof).map (telescope Expr.forallE) (telescope .lam)


/--
`@[mt]` (abbreviated from `modus tollens`) attribute automatically generates the mt version of an implication theorem.
Usage:
```lean
@[mt]
theorem Section.LHS.of.RHS {a : α} {b : β} (h : lhs a b) : rhs a b := proof
-- Generates:
theorem Section.NotRHS.of.NotLHS {a : α} {b : β} (h : ¬rhs a b): ¬lhs a b := mt Section.LHS.of.RHS h
```
-/
initialize registerBuiltinAttribute {
  name := `mt
  descr := "Automatically generate the contraposition of a theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ := Expr.mt decl.type (.const declName (levelParams.map .param))
    addAndCompile <| .thmDecl {
      name := (← getEnv).moduleTokens.mt.lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}
