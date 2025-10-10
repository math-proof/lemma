import sympy.Basic
import stdlib.Prod
import sympy.parsing.parser
open Lean Lean.Meta

def Expr.comm' (type proof : Lean.Expr) (parity : ℕ) : CoreM (List Bool × Lean.Expr × Lean.Expr) := do
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
    binders.filterMap fun ⟨comm, _, _, binderInfo⟩ => if binderInfo == .default then some comm else none,
    type, value
  )

initialize registerBuiltinAttribute {
  name := `comm'
  descr := "Automatically generate the commutative version of an equality theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨parity, type, value⟩ ← Expr.comm' decl.type (.const declName (levelParams.map .param)) stx.parity
    println! s!"parity = {parity}"
    println! s!"(← getEnv).moduleTokens = {(← getEnv).moduleTokens}"
    addAndCompile <| .thmDecl {
      name := (((← getEnv).moduleTokens.comm parity).foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.mp' (type proof : Lean.Expr) (parity : ℕ := 0) (reverse : Bool := false) : CoreM (Lean.Expr × Lean.Expr) := do
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
  let telescope := fun lam hint body => do
    body.println context s!"prior {hint}"
    let body := binders.zipIdx.foldl
      (fun body ⟨⟨binderName, binderType, binderInfo⟩, deBruijn⟩ =>
        lam binderName binderType body (if binderInfo == .default && given.containsBVar deBruijn then .implicit else binderInfo)
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
  let ⟨h_curr, h_next⟩ := given.decomposeAnd
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
  (.forallE h₀ h₀Type imply .default, .lam h₀ h₀Type proof .default).mapM (telescope Expr.forallE "type") (telescope .lam "value")

initialize registerBuiltinAttribute {
  name := `mp'
  descr := "Automatically generate the mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.parity
    Lean.logInfo s!"parity = {parity}"
    let ⟨type, value⟩ ← Expr.mp' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity
    addAndCompile <| .thmDecl {
      name := ((← getEnv).moduleTokens.mp.foldl Name.str default).lemmaName declName
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.mpr' (type proof : Lean.Expr) (parity : ℕ := 0) : CoreM (Lean.Expr × Lean.Expr) := Expr.mp' type proof parity true

initialize registerBuiltinAttribute {
  name := `mpr'
  descr := "Automatically generate the two implications of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.parity
    let ⟨type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity
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
    let ⟨type, value⟩ ← Expr.mp' decl.type (.const declName (levelParams.map .param))
    let ⟨parity, type, value⟩ ← Expr.comm' type value stx.parity
    addAndCompile <| .thmDecl {
      name := (((← getEnv).moduleTokens.mp.comm parity).foldl Name.str default).lemmaName declName
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
    -- let ⟨type, value⟩ ← Expr.mpr' decl.type (.const declName (levelParams.map .param))
    let ⟨type, value⟩ := Expr.mpr decl.type (.const declName (levelParams.map .param))
    let ⟨parity, type, value⟩ := Expr.comm type value stx.parity
    addAndCompile <| .thmDecl {
      name := (((← getEnv).moduleTokens.mpr.comm parity).foldl Name.str default).lemmaName declName
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
    -- Lean.logInfo "decl.type = \n{decl.type.format}"
    Lean.logInfo "decl.value! = \n{decl.value!.format}"
}
