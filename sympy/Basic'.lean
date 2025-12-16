import sympy.Basic
import stdlib.Prod
import sympy.parsing.parser
open Lean Lean.Meta

def Expr.comm' (type proof : Lean.Expr) (parity : ℕ := 0) : CoreM (List (Bool × Lean.Expr) × Lean.Expr × Lean.Expr) := do
  let ⟨binders, type⟩ := type.decompose_forallE
  let binders := binders.zipParity parity
  let ⟨type, symm⟩ := type.decomposeType
  let telescope := fun localBinders lam hint body => do
      let mut body := body
      let mut context := binders.map fun ⟨_, binderName, binderType, _⟩ => (binderName, binderType)
      body.println context s!"original {hint}"
      for ⟨declName, type, deBruijn⟩ in localBinders do
          let type := type.incDeBruijnIndex (deBruijn + 1)
          let declName :=
            match declName with
            | .str pre name => Name.str pre (name ++ "'")
            | _ => declName
          body := body.incDeBruijnIndex 1
          body := body.setDeBruijnIndex (deBruijn + 1) 0
          context := ⟨declName, type⟩ :: context
          body := .letE declName type (.app type.comm.symm (.bvar deBruijn)) body false
          body.println context hint
      body := binders.foldl (fun body ⟨comm, binderName, binderType, binderInfo⟩ => lam binderName (if comm then binderType.comm else binderType) body binderInfo) body
      body.println [] s!"final {hint}"
      return body
  let valueBinders := binders.zipIdx.filterMap fun ⟨⟨comm, binderName, binderType, _⟩, deBruijn⟩ => if comm then some (binderName, binderType, deBruijn) else none
  let (type, value) ← (type, .app symm (proof.mkApp ((List.range binders.length).map fun i => .bvar i).reverse)).mapM
    (telescope (valueBinders.filterMap fun args@⟨_, _, deBruijn⟩ => if type.containsBVar deBruijn then some args else none) Expr.forallE "type")
    (telescope valueBinders .lam "proof")
  return (
    binders.filterMap fun ⟨comm, _, binderType, binderInfo⟩ => if binderInfo == .default then some ⟨comm, binderType⟩ else none,
    type, value
  )

initialize registerBuiltinAttribute {
  name := `comm'
  descr := "Automatically generate the commutative version of an equality theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨parity, type, value⟩ ← Expr.comm' decl.type (.const declName (levelParams.map .param)) stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    println! s!"parity = {parity}"
    println! s!"moduleTokens = {moduleTokens}"
    let name := ((moduleTokens.comm parity).foldl Name.str default).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.mp' (type proof : Lean.Expr) (parity : ℕ := 0) (reverse : Bool := false) (and : Bool := false) : CoreM (ℕ × Lean.Expr × Lean.Expr) := do
  let ⟨binders, type⟩ := type.decompose_forallE
  let deBruijn := (binders.zipParity parity .instImplicit).zipIdx.filterMap fun ⟨⟨bit, _⟩, deBruijn⟩ => if bit then some deBruijn else none
  for deBruijn in deBruijn do
    if type.containsBVar deBruijn then
      let ⟨_, instType, _⟩ := binders[deBruijn]!
      panic! s!"The proof of the mp/mpr theorem must not contain the given TypeClass : {instType.getAppFn.constName!}."
  let decDeBruijnIndex := fun type => deBruijn.foldr (fun deBruijn type => type.decDeBruijnIndex 1 deBruijn) type
  let type := decDeBruijnIndex type
  let binders := deBruijn.foldr
    (fun deBruijn binders =>
      let ⟨lowerPart, higherPart⟩ := binders.splitAt deBruijn
      let lowerPart := lowerPart.map fun ⟨binderName, binderType, binderInfo⟩ => ⟨binderName, binderType.decDeBruijnIndex 1, binderInfo⟩
      lowerPart ++ higherPart.tail
    )
    binders
  let context := binders.map fun ⟨binderName, binderType, _⟩ => (binderName, binderType)
  type.println context "original type"
  let ⟨us, lhs, rhs⟩ := type.decomposeIff
  let ⟨given, imply, mp⟩ := if reverse then (rhs, lhs.incDeBruijnIndex 1, `Iff.mpr) else (lhs, rhs.incDeBruijnIndex 1, `Iff.mp)
  given.println context "hypothesis"
  let binders : List (Name × Lean.Expr × BinderInfo) := binders.zipIdx.map fun ⟨⟨binderName, binderType, binderInfo⟩, deBruijn⟩ =>
    (binderName, binderType, (if binderInfo == .default && given.containsBVar deBruijn then .implicit else binderInfo))
  let telescope := fun lam hint body => do
    body.println context s!"prior {hint}"
    let body := binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
    body.println [] s!"final {hint}"
    return body
  let proof ←
    if parity > 0 then
      let ⟨lamBinders, intro⟩ := proof.decompose_lam []
      let ⟨us, mp, mpr⟩ := intro.decomposeIff
      let mp := if reverse then mpr else mp
      Lean.logInfo s!"us = {us}"
      Lean.logInfo s!"mp = {mp}"
      for deBruijn in deBruijn do
        if mp.containsBVar deBruijn then
          let ⟨_, instType, _⟩ := lamBinders[deBruijn]!
          throwError "The proof of the mp/mpr theorem must not contain the given TypeClass[#{deBruijn}] {instType.getAppFn.constName!}."
      pure (decDeBruijnIndex mp)
    else
      pure ((Lean.Expr.const mp us).mkApp [lhs, rhs, proof.mkApp ((List.range binders.length).map fun i => .bvar i).reverse])
  let ⟨h_curr, h_next⟩ := if and then ⟨[given], []⟩ else given.decomposeAnd
  Lean.logInfo s!"and = {and}"
  let h_name := (List.range h_curr.length).map fun i => .str default ("h" ++ i.toSubscriptString)
  let pNameType := h_name.zip h_curr
  let ⟨h₀, h₀Type⟩ := pNameType.head!
  let pNameType := pNameType.tail
  let size := h_curr.length
  let deBruijn := (List.range size).drop 1
  let bvar := (deBruijn.reverse.zip (h_curr.zip h_next)).foldr
    (fun ⟨deBruijn, h_curr, h_next⟩ bvar =>
      (Lean.Expr.const `And.intro us).mkApp [
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
  return (
    binders.countP (·.snd.snd == .default),
    ← (.forallE h₀ h₀Type imply .default, .lam h₀ h₀Type proof .default).mapM (telescope Expr.forallE "type") (telescope .lam "value")
  )

initialize registerBuiltinAttribute {
  name := `mp'
  descr := "Automatically generate the mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    Lean.logInfo s!"parity = {parity}"
    Lean.logInfo s!"and = {and}"
    let ⟨_, type, value⟩ ← Expr.mp' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity (and := and)
    addAndCompile <| .thmDecl {
      name := ((← getEnv).moduleTokens.mp.foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.mpr' (type proof : Lean.Expr) (parity : ℕ := 0) (and : Bool := false) : CoreM (ℕ × Lean.Expr × Lean.Expr) := Expr.mp' type proof parity true and

initialize registerBuiltinAttribute {
  name := `mpr'
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity and
    addAndCompile <| .thmDecl {
      name := ((← getEnv).moduleTokens.mpr.foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mp.comm'
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨n, type, value⟩ ← Expr.mp' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity (and := and)
    println! s!"n = {n}, 1 <<< n = {1 <<< n}"
    let ⟨parity, type, value⟩ ← Expr.comm' type value (1 <<< n)
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    let name := ((moduleTokens.mp.comm parity).foldl Name.str default).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.comm'
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨n, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity and
    let ⟨parity, type, value⟩ ← Expr.comm' type value (1 <<< n)
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    addAndCompile <| .thmDecl {
      name := ((moduleTokens.mpr.comm parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.comm.is' (type mp mpr : Lean.Expr) (parity : ℕ := 0) : CoreM (List (Bool × Lean.Expr) × Lean.Expr × Lean.Expr) := do
  let ⟨binders, type⟩ := type.decompose_forallE
  let args := ((List.range binders.length).map fun i => .bvar i).reverse
  let binders := binders.zipParity parity
  let mp := mp.mkApp args
  let mpr := mpr.mkApp args
  let ⟨us, lhs, rhs⟩ := type.decomposeIff
  let lhs := lhs.comm
  let rhs := rhs.comm
  let telescope := fun localBinders lam hint body => do
      let mut body := body
      let mut context := binders.map fun ⟨_, binderName, binderType, _⟩ => (binderName, binderType)
      body.println context s!"original {hint}"
      for ⟨declName, type, deBruijn⟩ in localBinders do
          let type := type.incDeBruijnIndex (deBruijn + 1)
          let declName :=
            match declName with
            | .str pre name => Name.str pre (name ++ "'")
            | _ => declName
          body := body.incDeBruijnIndex 1
          body := body.setDeBruijnIndex (deBruijn + 1) 0
          context := ⟨declName, type⟩ :: context
          body := .letE declName type (.app type.comm.symm (.bvar deBruijn)) body false
          body.println context hint
      body := binders.foldl (fun body ⟨comm, binderName, binderType, binderInfo⟩ => lam binderName (if comm then binderType.comm else binderType) body binderInfo) body
      body.println [] s!"final {hint}"
      return body
  let valueBinders := binders.zipIdx.filterMap fun ⟨⟨comm, binderName, binderType, _⟩, deBruijn⟩ => if comm then some (binderName, binderType, deBruijn) else none
  let (type, value) ← ((Lean.Expr.const `Iff us).mkApp [lhs, rhs], (Lean.Expr.const `Iff.intro us).mkApp [lhs, rhs, mp, mpr]).mapM
    (telescope (valueBinders.filterMap fun args@⟨_, _, deBruijn⟩ => if type.containsBVar deBruijn then some args else none) Expr.forallE "type")
    (telescope valueBinders .lam "proof")
  return (
    binders.filterMap fun ⟨comm, _, binderType, binderInfo⟩ => if binderInfo == .default then some ⟨comm, binderType⟩ else none,
    type, value
  )

initialize registerBuiltinAttribute {
  name := `comm.is'
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams

    let proof : Lean.Expr := .const declName (levelParams.map .param)
    let ⟨n, type, value⟩ ← Expr.mpr' decl.type proof (and := true)
    let ⟨_, type, mpr⟩ := Expr.comm type value (1 <<< n)

    let ⟨n, type, value⟩ ← Expr.mp' decl.type proof (and := true)
    let ⟨_, type, mp⟩ := Expr.comm type value (1 <<< n)

    let ⟨parity, type, value⟩ ← Expr.comm.is' decl.type mp mpr stx.getNum
    let ⟨moduleTokens, parity⟩ ← parity.extractParity
    let name := List.comm.is moduleTokens parity
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := (name.foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.mt' (type proof : Lean.Expr) : CoreM (Lean.Expr × Lean.Expr) := do
  let ⟨binders, type⟩ := type.decompose_forallE
  let context := binders.map fun ⟨binderName, binderType, _⟩ => (binderName, binderType)
  type.println context "original type"
  let b := type
  println! s!"binders = {binders}"
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
  println! s!"h = {h}"
  let (binders, type, a, mp) :=
    if let ⟨h, premise, .default⟩ :: rest := binders then
      let a := premise.incDeBruijnIndex 1
      let mp :=
        match a with
        | .app (.const `Not _) arg =>
          fun h : Lean.Expr =>
            (Lean.Expr.const `Iff.mp []).mkApp [
              (Lean.Expr.const `Not []).mkApp [(Lean.Expr.const `Not []).mkApp [arg]],
              arg,
              (Lean.Expr.const `Classical.not_not []).mkApp [arg],
              h
            ]
        | _ =>
          id
      ((h, Not (type.decDeBruijnIndex 1), BinderInfo.default) :: rest, Not a, a, mp)
    else
      panic! "The theorem must have at least one hypothesis."
  println! s!"binders = {binders}"
  let ⟨_, premise, _⟩ := binders[0]!
  premise.println (binders.tail.map fun ⟨binderName, binderType, _⟩ => (binderName, binderType)) "premise"
  type.println context "new type"
  let telescope := fun lam hint body => do
    body.println context s!"prior {hint}"
    let body := binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
    body.println [] s!"final {hint}"
    return body
  -- mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a
  let proof := ((Lean.Expr.const `mt []).mkApp [a, b, proof.mkApp ((List.range binders.length).map fun i => (Lean.Expr.bvar i)).tail.reverse, h])
  let proof := mp proof
  (type, proof).mapM (telescope Expr.forallE "type") (telescope .lam "value")

initialize registerBuiltinAttribute {
  name := `mt'
  descr := "Automatically generate the contraposition of a theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let env ← getEnv
    let constructor_order :=
      match ← findDocString? env declName with
      | some doc =>
        doc.containsSubstr "constructor order"
      | none =>
        false
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.mt' decl.type (.const declName (levelParams.map .param))
    let name := ((← getEnv).moduleTokens.mt constructor_order).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `debug
  descr := "debug"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    -- Lean.logInfo s!"decl.type = \n{decl.type.format}"
    Lean.logInfo s!"decl.value! = \n{decl.value!.format}"
}
