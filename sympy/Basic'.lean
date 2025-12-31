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
      body.println context s!"prior {hint}"
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
    let name := ((← getEnv).moduleTokens.mp.foldl Name.str default).lemmaName declName
    Lean.logInfo s!"name = {name}"
    Lean.logInfo s!"(← getEnv).moduleTokens = {(← getEnv).moduleTokens}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.mpr' (type proof : Lean.Expr) (parity : ℕ := 0) (and : Bool := false) : CoreM (ℕ × Lean.Expr × Lean.Expr) := Expr.mp' type proof parity true and

initialize registerBuiltinAttribute {
  name := `mpr'
  descr := "Automatically generate the mpr implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity and
    let name := ((← getEnv).moduleTokens.mpr.foldl Name.str default).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mp.comm'
  descr := "Automatically generate the commutative mp implication of an equivalence theorem"
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
  descr := "Automatically generate the commutative mpr implication of an equivalence theorem"
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
      body.println context s!"prior {hint}"
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
  descr := "Automatically generate the commutative version of an equivalence theorem"
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

def Expr.mt' (type proof : Lean.Expr) (parity : ℕ := 0) : CoreM (ℕ × Lean.Expr × Lean.Expr) := do
  let ⟨binders, type⟩ := type.decompose_forallE
  let defaultCount := binders.countP (·.snd.snd == .default)
  let parity :=
    if parity = 0 then
      1 <<< (defaultCount - 1)
    else
      parity
  let index := defaultCount - 1 - parity.log2
  println! "index = {index}"
  let context := binders.map fun ⟨binderName, binderType, _⟩ => (binderName, binderType)
  type.println context "old type"
  let b := type
  println! s!"binders = {binders}"
  let h_bvar := Lean.Expr.bvar index
  let h :=
    let ⟨us, args, lemmaName⟩ := type.decomposeNot
    if lemmaName == default then
      h_bvar
    else
      type.mpr h_bvar us args lemmaName
  println! s!"h = {h}"
  let (binders, type, a, mp) :=
    let ⟨h, premise, df⟩ := binders[index]!
    let premise := premise.incDeBruijnIndex index.succ
    let mp :=
      let ⟨us, args, lemmaName⟩ := premise.decomposeNot
      if lemmaName == default then
        id
      else
        fun h => premise.mp h us args lemmaName
    (binders.set index (h, (type.decDeBruijnIndex index.succ).Not, df), premise.Not, premise, mp)
  println! s!"binders = {binders}"
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
  proof.println context "proof"
  a.println context "a"
  let proof := ((Lean.Expr.const `mt []).mkApp [
    a,
    b,
    if index > 0 then
      let bvar := ((List.range binders.length).map fun i => (Expr.bvar i))
      let ⟨take, drop⟩ := bvar.splitAt index
      let drop := drop.tail.map fun e => e.incDeBruijnIndex 1
      let ⟨binderName, _, binderInfo⟩ := binders[index]!
      .lam binderName a (proof.mkApp ((take ++ drop).reverse ++ [h_bvar])) binderInfo
    else
      proof.mkApp ((List.range binders.length).map fun i => (.bvar i)).tail.reverse,
    h
  ])
  return (index, ← (type, mp proof).mapM (telescope Expr.forallE "type") (telescope .lam "value"))

initialize registerBuiltinAttribute {
  name := `mt'
  descr := "Automatically generate the contraposition (modus tollens) of an implication theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constructor_order ← constructor_order declName
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    println! s!"parity = {parity}"
    let ⟨parity, type, value⟩ ← Expr.mt' decl.type (.const declName (levelParams.map .param)) parity
    let name := ((← getEnv).moduleTokens.mt constructor_order parity).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mp.mt'
  descr := "Automatically generate the mt version of the mp implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constructor_order ← constructor_order declName
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let proof : Lean.Expr := .const declName (levelParams.map .param)
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ := Expr.mp decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity (and := and)
    let ⟨_, type, value⟩ ← Expr.mt' type value
    let moduleTokens := (← getEnv).moduleTokens.mp
    println! s!"moduleTokens.mp = {moduleTokens}"
    let name := (moduleTokens.mt constructor_order).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.mt'
  descr := "Automatically generate the mt version of the mpr implication of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let constructor_order ← constructor_order declName
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let proof : Lean.Expr := .const declName (levelParams.map .param)
    let parity := stx.getNum
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity (stx.getIdent == `and)
    let ⟨_, type, value⟩ ← Expr.mt' type value
    let moduleTokens := (← getEnv).moduleTokens.mpr
    let name := (moduleTokens.mt constructor_order).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.disjunction' (type proof : Lean.Expr) (parity : ℕ := 0) (left : Bool := true) : CoreM (ℕ × Lean.Expr × Lean.Expr) := do
  let ⟨binders, type⟩ := type.decompose_forallE
  let defaultCount := binders.countP (·.snd.snd == .default)
  let parity :=
    if parity = 0 then
      1 <<< (defaultCount - 1)
    else
      parity
  let index := defaultCount - 1 - parity.log2
  println! "index = {index}"
  let context := binders.map fun ⟨binderName, binderType, _⟩ => (binderName, binderType)
  let ⟨h, given, info⟩ := binders[index]!
  let ⟨inl, inr⟩ : Lean.Expr × Lean.Expr:=
    if let .app (.app (.const `Or _) a) b := given then
      ⟨a, b⟩
    else
      panic! "disjunction not found"
  let binders := binders.set index ⟨h, if left then inl else inr, info⟩
  type.println context "old type"
  println! s!"binders = {binders}"
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
  let h_bvar := Lean.Expr.bvar index
  let intro := if left then `Or.inl else `Or.inr
  let proof : Lean.Expr :=
    if index > 0 then
      let bvar := ((List.range binders.length).map fun i => (Expr.bvar i))
      let ⟨take, drop⟩ := bvar.splitAt index
      let drop := drop.tail.map fun e => e.incDeBruijnIndex 1
      let ⟨binderName, type, binderInfo⟩ := binders[index]!
      Lean.Expr.lam binderName type (proof.mkApp ((take ++ drop).reverse ++ [h_bvar])) binderInfo
    else
      let args := ((List.range binders.length).map fun i => (.bvar i))
      let args := args.set index ((Lean.Expr.const intro []).mkApp [inl.incDeBruijnIndex 1, inr.incDeBruijnIndex 1, h_bvar])
      proof.mkApp args.reverse
  proof.println context "proof"
  return (index, ← (type, proof).mapM (telescope Expr.forallE "type") (telescope .lam "value"))

initialize registerBuiltinAttribute {
  name := `left'
  descr := "Automatically generate the left introduction of a disjunction theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    println! s!"parity = {parity}"
    let ⟨parity, type, value⟩ ← Expr.disjunction' decl.type (.const declName (levelParams.map .param)) parity
    let name := ((← getEnv).moduleTokens.left).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `right'
  descr := "Automatically generate the right introduction of a disjunction theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    println! s!"parity = {parity}"
    let ⟨parity, type, value⟩ ← Expr.disjunction' decl.type (.const declName (levelParams.map .param)) parity false
    let name := ((← getEnv).moduleTokens.right).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.left'
  descr := "Automatically generate the left introduction of a disjunction theorem from the mpr part of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity and
    let moduleTokens := (← getEnv).moduleTokens.mpr
    println! s!"moduleTokens = {moduleTokens}"
    let ⟨parity, type, value⟩ ← Expr.disjunction' type value
    let name := (moduleTokens.left).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `mpr.right'
  descr := "Automatically generate the right introduction of a disjunction theorem from the mpr part of an equivalence theorem"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let parity := stx.getNum
    let and := stx.getIdent == `and
    let ⟨_, type, value⟩ ← Expr.mpr' decl.type (if parity > 0 then decl.value! else .const declName (levelParams.map .param)) parity and
    let moduleTokens := (← getEnv).moduleTokens.mpr
    println! s!"moduleTokens = {moduleTokens}"
    let ⟨parity, type, value⟩ ← Expr.disjunction' type value 0 false
    let name := (moduleTokens.right).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

def Expr.subst' (type proof : Lean.Expr) (subst : Lean.Expr → Lean.Expr) : CoreM (Lean.Expr × Lean.Expr) := do
  let ⟨binders, type⟩ := type.decompose_forallE
  let context := binders.map fun ⟨binderName, binderType, _⟩ => (binderName, binderType)
  type.println context "old type"
  println! s!"binders = {binders}"
  let type := subst type
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
  let proof : Lean.Expr :=
    let args := ((List.range binders.length).map fun i => (.bvar i))
    proof.mkApp args.reverse
  proof.println context "proof"
  (type, proof).mapM (telescope Expr.forallE "type") (telescope .lam "value")

initialize registerBuiltinAttribute {
  name := `fin'
  descr := "Automatically generate the theorem with .getElem substituted by .get"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.subst' decl.type (.const declName (levelParams.map .param)) Lean.Expr.getElem2get
    let moduleTokens := (← getEnv).moduleTokens
    println! s!"moduleTokens = {moduleTokens}"
    let name := ((moduleTokens.concat "fin").foldl Name.str default).lemmaName declName
    println! s!"name = {name}"
    addAndCompile <| .thmDecl {
      name := name
      levelParams := levelParams
      type := type
      value := value
    }
}

initialize registerBuiltinAttribute {
  name := `val'
  descr := "Automatically generate the theorem with Fin type substituted by its val type"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let decl ← getConstInfo declName
    let levelParams := decl.levelParams
    let ⟨type, value⟩ ← Expr.subst' decl.type (.const declName (levelParams.map .param)) Lean.Expr.fin2val
    let moduleTokens := (← getEnv).moduleTokens
    println! s!"moduleTokens = {moduleTokens}"
    let name := ((moduleTokens.concat "val").foldl Name.str default).lemmaName declName
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
    Lean.logInfo s!"decl.type = \n{decl.type.format}"
    Lean.logInfo s!"decl.value! = \n{decl.value!.format}"
}
