import Mathlib.Tactic
import Def.Lean.Syntax
import Def.Lean.Environment
import Def.Lean.Meta.Expr.Part4
import Def.Lean.ConstantInfo.Part5
import Structure.Tactic.Attr.Basic
open Lean
open Lean.Meta


/-- Peel nested `Filter.Eventually` (`∀ᵐ`) wrappers. Layers are outer-first; core is the innermost body. -/
partial def Lean.Expr.decomposeEventually : Lean.Expr → List EventuallyLayer × Lean.Expr
  | .app (.app (.app (.const `Filter.Eventually us) α) (.lam binderName binderType body binderInfo)) f =>
    let ⟨layers, core⟩ := body.decomposeEventually
    (⟨us, α, binderName, binderType, binderInfo, f⟩ :: layers, core)
  | e =>
    ([], e)

def EventuallyLayer.wrap (layer : EventuallyLayer) (body : Lean.Expr) : Lean.Expr :=
  let p := Lean.Expr.lam layer.binderName layer.binderType body layer.binderInfo
  (Lean.Expr.const `Filter.Eventually layer.us).mkApp [layer.α, p, layer.f]

def List.wrapEventually (layers : List EventuallyLayer) (body : Lean.Expr) : Lean.Expr :=
  layers.foldr (fun layer body => layer.wrap body) body

/--
Under `n` pairs `(xᵢ, hᵢ)` as `x₀,h₀,…,xₙ₋₁,hₙ₋₁`, map bvars from an `n`-deep
Eventually body (`bvar k` = `xₙ₋₁₋ₖ`) to `bvar (2*k+1)`, and shift outer free bvars by `n`.
-/
partial def Lean.Expr.liftAeIffBVars (n : Nat) : Lean.Expr → Lean.Expr
  | .bvar i => if i < n then .bvar (2 * i + 1) else .bvar (i + n)
  | .app f a => .app (f.liftAeIffBVars n) (a.liftAeIffBVars n)
  | .lam n' t b bi => .lam n' (t.liftAeIffBVars n) (b.liftAeIffBVars n) bi
  | .forallE n' t b bi => .forallE n' (t.liftAeIffBVars n) (b.liftAeIffBVars n) bi
  | .letE n' t v b nd =>
      .letE n' (t.liftAeIffBVars n) (v.liftAeIffBVars n) (b.liftAeIffBVars n) nd
  | .mdata m e => .mdata m (e.liftAeIffBVars n)
  | .proj N i e => .proj N i (e.liftAeIffBVars n)
  | e => e

/--
`hAeIff` proves `wrapEventually layers (Iff …)`.
Proof of `wrapEventually layers (Imp)` via nested `Filter.Eventually.mono`.
Uses `Iff` projections at the core, and `incDeBruijnIndex 1 1` when crossing each `(x,hx)` pair
so remaining Eventually-bvars stay aligned.
-/
def List.buildEventuallyMp (layers : List EventuallyLayer) (hAeIff : Lean.Expr)
    (usIff : List Level) (lhs rhs : Lean.Expr) (reverse : Bool) : Lean.Expr :=
  let iffCore := (Lean.Expr.const `Iff usIff).mkApp [lhs, rhs]
  let given := if reverse then rhs else lhs
  let imply := (if reverse then lhs else rhs).incDeBruijnIndex 1
  let impCore := Lean.Expr.forallE `h given imply .default
  let mpIdx : Nat := if reverse then 1 else 0
  -- `shift` = how many (x,hx) pairs we have crossed; remaining Eventually-relative exprs
  -- are adjusted with repeated `incDeBruijnIndex 1 1`.
  let adjust (e : Lean.Expr) (pairs : Nat) : Lean.Expr :=
    (List.range pairs).foldl (fun e _ => e.incDeBruijnIndex 1 1) e
  let rec go (rest : List EventuallyLayer) (h : Lean.Expr) (pairs : Nat) : Lean.Expr :=
    match rest with
    | [] =>
      .proj ``Iff mpIdx h
    | layer :: rest' =>
      let iffU := adjust iffCore pairs
      let impU := adjust impCore pairs
      let pBody := rest'.wrapEventually iffU
      let qBody := rest'.wrapEventually impU
      -- also adjust layer α/f/binderType for surrounding pairs
      let α := adjust layer.α pairs
      let binderType := adjust layer.binderType pairs
      let f := adjust layer.f pairs
      let pPred := Lean.Expr.lam layer.binderName binderType pBody layer.binderInfo
      let qPred := Lean.Expr.lam layer.binderName binderType qBody layer.binderInfo
      let inner := go rest' (.bvar 0) (pairs + 1)
      let hq :=
        Lean.Expr.lam layer.binderName binderType
          (Lean.Expr.lam `hx pBody inner .default)
          layer.binderInfo
      (Lean.Expr.const `Filter.Eventually.mono layer.us).mkApp [
        α, pPred, qPred, f, h, hq
      ]
  go layers hAeIff 0


/-- Replace the first module token containing substring `Iff` by substituting that substring with `replacement`. -/
def List.replaceIffToken (tokens : List String) (replacement : String) : Option (List String) :=
  let rec loop (acc : List String) : List String → Option (List String)
    | [] => none
    | t :: ts =>
      let parts := t.splitOn "Iff"
      if parts.length ≥ 2 then
        some (acc.reverse ++ (parts.head! ++ replacement ++ String.intercalate "Iff" parts.tail!) :: ts)
      else
        loop (t :: acc) ts
  loop [] tokens

def Expr.mp (type value : Expr) (parity : ℕ := 0) (reverse : Bool := false) (and : Bool := false) : ℕ × Expr × Expr :=
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
  let ⟨layers, core⟩ := type.decomposeEventually
  let ⟨us, lhs, rhs⟩ := core.decomposeIff
  let ⟨given, imply, mp⟩ := if reverse then (rhs, lhs.incDeBruijnIndex 1, `Iff.mpr) else (lhs, rhs.incDeBruijnIndex 1, `Iff.mp)
  let nLayers := layers.length
  let binders : List (Name × Expr × BinderInfo) := binders.zipIdx.map fun ⟨⟨binderName, binderType, binderInfo⟩, deBruijn⟩ =>
    (binderName, binderType, (if binderInfo == .default && given.containsBVar (deBruijn + nLayers) then .implicit else binderInfo))
  let telescope := fun lam body =>
    binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
  let binderArgs := ((List.range binders.length).map fun i => Expr.bvar i).reverse
  let hThm :=
    if parity > 0 then
      let ⟨_, intro⟩ := value.decompose_lam []
      let ⟨_, mp, mpr⟩ := intro.decomposeIff
      let mp := if reverse then mpr else mp
      decDeBruijnIndex mp
    else
      value.mkApp binderArgs
  if !layers.isEmpty then
    if parity > 0 then
      panic! "mp/mpr Eventually peeling does not support parity > 0 yet"
    else
      let givenCore := if reverse then rhs else lhs
      let implyCore := if reverse then lhs else rhs
      let impCore := Expr.forallE `h givenCore (implyCore.incDeBruijnIndex 1) .default
      let typeBody := layers.wrapEventually impCore
      let valueBody := layers.buildEventuallyMp hThm us lhs rhs reverse
      (
        binders.countP (·.snd.snd == .default),
        (typeBody, valueBody).map (telescope Expr.forallE) (telescope .lam)
      )
  else
    let value :=
      if parity > 0 then
        hThm
      else
        (Expr.const mp us).mkApp [lhs, rhs, hThm]
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
    let value := Expr.app (value.incDeBruijnIndex size) bvar
    let value := (deBruijn.zip pNameType).foldr (fun ⟨deBruijn, name, type⟩ value => (.lam name (type.incDeBruijnIndex deBruijn) value .default)) value
    (
      binders.countP (·.snd.snd == .default),
      (.forallE h₀ h₀Type imply .default, .lam h₀ h₀Type value .default).map (telescope Expr.forallE) (telescope .lam)
    )


def List.mp (list : List String) : List String := list.decomposeOf [] (fun list _ => list.commutateIs "of") 1

/--
Module-name tokens for an `mp.left` / `mp.right` projection.

Given source tokens `[Section, LHS, "is", T1, T2]` (a biconditional whose right-hand
side is a conjunction `T1 ∧ T2`), `List.mp` produces
`[Section, T1, T2, "of", LHS]`. Then:

- `left = true`: drop the second conjunct type `T2` →
  `[Section, T1, "of", LHS]`
- `left = false`: drop the first conjunct type `T1` →
  `[Section, T2, "of", LHS]`

When `T1 = T2` both targets coincide, so a `.fst` / `.snd` suffix is appended.
-/
def List.mpProjTokens (tokens : List String) (left : Bool) : List String :=
  let mpTokens := tokens.mp
  let ofIdx := mpTokens.idxOf "of"
  let pre := mpTokens.take ofIdx                  -- [Section, T1, T2]
  let rest := mpTokens.drop (ofIdx + 1)          -- [LHS]
  let secLen := pre.length - 2
  let sectionTypes :=
    if left then pre.take (secLen + 1)            -- [Section, T1]
    else           pre.take secLen ++ [pre.getLast!]  -- [Section, T2]
  sectionTypes ++ "of" :: rest

def List.comm.is (list : List String) (parity : List Bool) : List String :=
  list.decomposeOf parity fun list _ =>
    let i := list.idxOf "is"
    let ⟨lhs, rhs⟩ := list.splitAt i
    let lhs := lhs.transformPrefix
    let rhs := rhs.tail.transformPrefix
    lhs ++ "is" :: rhs

def List.is.comm (list : List String) (parity : List Bool) : List String :=
  list.decomposeOf parity fun list _ =>
    let i := list.idxOf "is"
    let ⟨lhs, rhs⟩ := list.splitAt i
    let lhs := lhs.transformPrefix
    let rhs := rhs.tail.transformPrefix
    rhs ++ "is" :: lhs


def Expr.mpr (type value : Expr) (parity : ℕ := 0) (and : Bool := false) : ℕ × Expr × Expr := Expr.mp type value parity true and

def List.mpr (list : List String) : List String :=
  list.decomposeOf []
    (fun list _ =>
      let i := list.idxOf "is"
      let ⟨first, second⟩ := list.splitAt i
      first ++ "of" :: second.tail
    ) 1


def Expr.comm.is (type mp mpr : Expr) (parity : ℕ := 0) : List (Bool × Expr) × Expr × Expr :=
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

def Expr.is.comm (type mp mpr : Expr) (parity : ℕ := 0) : List (Bool × Expr) × Expr × Expr :=
  let ⟨parity, type, value⟩ := Expr.comm.is type mp mpr parity
  let ⟨_, type, value⟩ := Expr.comm type value 0
  (parity, type, value)


partial def List.Not (list : List String) : List String :=
  if list.length == 1 then
    [list.head!.Not]
  else
    match list[1]! with
    | "eq"  =>
      list[0]! :: "ne" :: list.drop 2
    | "ne" =>
      list[0]! :: "eq" :: list.drop 2
    | "ou" =>
      let ⟨first, second⟩ := list.splitAt 1
      first.Not ++ second.tail.Not
    | _ =>
      panic! s!"Expected the operator 'eq' or 'ne', got: {list[1]!}"


def List.is.mt (list : List String) (parity : List Bool := []) : List String :=
  list.decomposeOf parity fun list _ =>
    let i := list.idxOf "is"
    let ⟨lhs, rhs⟩ := list.splitAt i
    let lhs := lhs.Not
    let rhs := rhs.tail.Not
    lhs ++ "is" :: rhs

def List.mt (list : List String) (constructorOrder : Bool := false) (index : ℕ := 0) : Name :=
  let i := list.idxOf "of"
  let ⟨first, ofPart⟩ := list.splitAt i
  let domain := first[0]!
  let first := first.tail
  let of := ofPart[0]!
  let ofPart := ofPart.tail.parseInfixSegments
  let i := if constructorOrder then ofPart.length - 1 - index else index
  let (first, ofPart) := (ofPart[i]!, ofPart.set i first.Not)
  (domain :: first.Not ++ of :: ofPart.flatten).foldl Name.str default

def Lean.Expr.Not : Expr → Expr
  | .app (.const `Not _) arg =>
    arg
  | .app (.app (.app (.const `Ne us) α) a) b =>
    (Expr.const `Eq us).mkApp [α, a, b]
  | (.app (.app (.const `Or _) p) q) =>
    (Expr.const `And []).mkApp [(Expr.const `Not []).mkApp [p], (Expr.const `Not []).mkApp [q]]
  | type =>
    (Expr.const `Not []).mkApp [type]

def Lean.Expr.mp (type h : Expr) (us : List Level) (args : List Expr) (lemmaName : Name) (reverse : Bool := false) :=
  (Expr.const (if reverse then `Iff.mpr else `Iff.mp) []).mkApp [
    (Expr.const `Not []).mkApp [type],
    type.Not,
    (Expr.const lemmaName us).mkApp args,
    h
  ]

def Lean.Expr.mpr (type h : Expr) (us : List Level) (args : List Expr) (lemmaName : Name) :=
  type.mp h us args lemmaName true

def Lean.Expr.decomposeNot : Expr → List Level × List Expr × Name
  | .app (.const `Not us) arg => ⟨us, [arg], `Classical.not_not⟩
  | .app (.app (.app (.const `Ne us) α) a) b => ⟨us, [α, a, b], `not_ne_iff⟩
  | .app (.app (.const `Or us) p) q => ⟨us, [p, q], `not_or⟩
  | _ => ⟨[], [], default⟩

def Expr.mt (type value : Expr) (parity : ℕ := 0) : ℕ × Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let defaultCount := binders.countP (·.snd.snd == .default)
  let parity :=
    if parity = 0 then
      1 <<< (defaultCount - 1)
    else
      parity
  let index := defaultCount - 1 - parity.log2
  let b := type
  let h_bvar := Expr.bvar index
  let h :=
    let ⟨us, args, lemmaName⟩ := type.decomposeNot
    if lemmaName == default then
      h_bvar
    else
      type.mpr h_bvar us args lemmaName
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
  let telescope := fun lam body =>
    binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
  -- mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a
  let value := ((Expr.const `mt []).mkApp [
    a,
    b,
    if index > 0 then
      let bvar := ((List.range binders.length).map fun i => (Expr.bvar i))
      let ⟨take, drop⟩ := bvar.splitAt index
      let drop := drop.tail.map fun e => e.incDeBruijnIndex 1
      let ⟨binderName, _, binderInfo⟩ := binders[index]!
      .lam binderName a (value.mkApp ((take ++ drop).reverse ++ [h_bvar])) binderInfo
    else
      value.mkApp ((List.range binders.length).map fun i => (.bvar i)).tail.reverse,
    h
  ])
  (index, (type, mp value).map (telescope Expr.forallE) (telescope .lam))

def Expr.is.mt (type value : Expr) : Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let ⟨us, lhs, rhs⟩ := type.decomposeIff
  let newType := (Expr.const `Iff us).mkApp [lhs.Not, rhs.Not]
  let args := ((List.range binders.length).map fun i => .bvar i).reverse
  let h := value.mkApp args
  let newValue := (Expr.const `Iff.not us).mkApp [lhs, rhs, h]
  let telescope := fun lam body =>
    binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
  (newType, newValue).map (telescope Expr.forallE) (telescope .lam)


def constructor_order (declName : Name) : CoreM Bool := do
  let env ← getEnv
  match ← findDocString? env declName with
  | some doc =>
    return doc.contains "constructor order"
  | none =>
    return false


def List.disjunction (list : List String) (left : Bool := true): Name :=
  let i := list.idxOf "of"
  let ⟨first, ofPart⟩ := list.splitAt i
  let of := ofPart[0]!
  let disjunctions := ofPart.tail
  let rest := disjunctions.tail
  let disjunction := disjunctions[0]!
  let intro :=
    if disjunction.startsWith "Or" then
      let disjunction := (disjunction.drop 2).toString
      let index := (disjunction.find 'S').offset.byteIdx
      let left := disjunction.eraseIdx index
      left :: rest
    else if disjunctions[1]! == "ou" then
      if left then
        disjunctions.take 1
      else
        disjunctions.drop 2
    else
      panic! s!"Expected 'Or' / 'ou' as the disjunction, got: {ofPart}"
  (first ++ of :: intro).foldl Name.str default

def List.left (list : List String) : Name :=
  list.disjunction true

def List.right (list : List String) : Name :=
  list.disjunction false

def Expr.disjunction (type value : Expr) (parity : ℕ := 0) (left : Bool := true) : ℕ × Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let defaultCount := binders.countP (·.snd.snd == .default)
  let parity :=
    if parity = 0 then
      1 <<< (defaultCount - 1)
    else
      parity
  let index := defaultCount - 1 - parity.log2
  let ⟨h, given, info⟩ := binders[index]!
  let ⟨inl, inr⟩ : Expr × Expr:=
    if let .app (.app (.const `Or _) a) b := given then
      ⟨a, b⟩
    else
      panic! "disjunction not found"
  let binders := binders.set index ⟨h, if left then inl else inr, info⟩
  let telescope := fun lam body =>
    binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
  let h_bvar := .bvar index
  let intro := if left then `Or.inl else `Or.inr
  let value : Expr :=
    if index > 0 then
      let bvar := (List.range binders.length).map fun i => (Expr.bvar i)
      let ⟨take, drop⟩ := bvar.splitAt index
      let drop := drop.tail.map fun e => e.incDeBruijnIndex 1
      let ⟨binderName, type, binderInfo⟩ := binders[index]!
      Expr.lam binderName type (value.mkApp ((take ++ drop).reverse ++ [h_bvar])) binderInfo
    else
      let args := ((List.range binders.length).map fun i => (.bvar i))
      let args := args.set index ((Expr.const intro []).mkApp [inl.incDeBruijnIndex 1, inr.incDeBruijnIndex 1, h_bvar])
      value.mkApp args.reverse
  (index, (type, value).map (telescope Expr.forallE) (telescope .lam))


/-- Split module tokens at the `"of"` segment into a prefix and the `of · givens` tail. -/
def List.splitAtOf (list : List String) : List String × List String :=
  list.splitAt (list.idxOf "of")

/--
`[Section, …, Type1, Type2, "of", Givens] → [Section, …, Type1, "of", Givens]`:
drop the second conjunct segment of a conjunctive conclusion.
-/
def List.andLeftTokens (list : List String) : List String :=
  let (pre, rest) := list.splitAtOf
  -- pre length >= 4: Section + Type1 + Type2 + Type3
  if pre.length ≥ 4 then
    pre.dropLast.dropLast ++ rest
  else
    pre.dropLast ++ rest

/--
`[Section, …, Type1, Type2, "of", Givens] → [Section, …, Type2, "of", Givens]`:
drop the first conjunct segment of a conjunctive conclusion.
-/
def List.andRightTokens (list : List String) : List String :=
  let (pre, rest) := list.splitAtOf
  pre.dropLast.dropLast ++ [pre.getLast!] ++ rest

/--
`[Section, …, Type1, Type2, Type3, "of", Givens] → [Section, …, Type2, "of", Givens]`:
middle conjunct of a right-associative triple `A ∧ B ∧ C` (`And.right.left`).
-/
def List.andRightLeftTokens (list : List String) : List String :=
  let (pre, rest) := list.splitAtOf
  pre.dropLast.dropLast.dropLast ++ [pre.dropLast.getLast!] ++ rest

/--
`[Section, …, Type1, Type2, Type3, "of", Givens] → [Section, …, Type3, "of", Givens]`:
rightmost conjunct of a right-associative triple `A ∧ B ∧ C` (`And.right.right`).
-/
def List.andRightRightTokens (list : List String) : List String :=
  let (pre, rest) := list.splitAtOf
  pre.dropLast.dropLast.dropLast ++ [pre.getLast!] ++ rest

/-- Peel consecutive top-level `letE`s (term-level `have`/`let` in the statement). -/
def Lean.Expr.decompose_letE (lets : List (Name × Lean.Expr × Lean.Expr) := []) :
    Lean.Expr → List (Name × Lean.Expr × Lean.Expr) × Lean.Expr
  | .letE name ty val body _ => body.decompose_letE (⟨name, ty, val⟩ :: lets)
  | e => (lets, e)

/--
Given a theorem `value : ∀ binders, (have/let …); A ∧ B`, produce the projected
theorem `∀ binders, (have/let …); A` (`left = true`) or `… B` (`left = false`),
proved by the anonymous projection `.1` / `.2`. The statement's term-level
`have`/`let` bindings are preserved in the generated type.
-/
def Expr.andProj (type value : Expr) (left : Bool) : Expr × Expr :=
  let (binders, rest) := type.decompose_forallE
  let (lets, concl) := rest.decompose_letE
  let (a, b) :=
    match concl with
    | .app (.app (.const ``And _) a) b => (a, b)
    | _ => panic! "And projection expects a conjunctive conclusion `A ∧ B`"
  let projected := if left then a else b
  let withLets :=
    lets.foldl (fun body ⟨name, ty, val⟩ => Expr.letE name ty val body false) projected
  let typeTelescope :=
    binders.foldl (fun body ⟨name, ty, bi⟩ => Expr.forallE name ty body bi) withLets
  let args := (List.range binders.length).map Expr.bvar |>.reverse
  let applied := value.mkApp args
  let proj := Expr.proj ``And (if left then 0 else 1) applied
  let valueTelescope :=
    binders.foldl (fun body ⟨name, ty, bi⟩ => Expr.lam name ty body bi) proj
  (typeTelescope, valueTelescope)

/--
Generated declaration name for an `And.left`/`And.right` projection.

`Section.Type1.Type2.of.Givens` maps to `Section.Type1.of.Givens` (left) or
`Section.Type2.of.Givens` (right). When `Type1 = Type2` both targets coincide, so a
`.fst` / `.snd` suffix is appended.

For a triple `Type1.Type2.Type3.of.Givens`, `And.left` keeps Type1 only and appends
`.fst` when `Type1 = Type2` (not when Type1 merely equals Type3).
-/
def Name.andProjName (moduleTokens : List String) (declName : Name) (left : Bool) : Name :=
  let leftTokens := moduleTokens.andLeftTokens
  let rightTokens := moduleTokens.andRightTokens
  let base := (if left then leftTokens else rightTokens).foldl Name.str default
  let (pre, _) := moduleTokens.splitAtOf
  let base :=
    if left then
      -- And.left: `.fst` when Type1 = Type2
      if pre.length ≥ 4 then
        if leftTokens == moduleTokens.andRightLeftTokens then base.str "fst" else base
      else if leftTokens == rightTokens then
        base.str "fst"
      else
        base
    else
      -- And.right (binary): `.snd` when Type1 = Type2
      if leftTokens == rightTokens then base.str "snd" else base
  base.lemmaName declName

/--
Generated declaration name for an `And.right.left` / `And.right.right` projection.

`Section.Type1.Type2.Type3.of.Givens` maps to `Section.Type2.of.Givens` (right.left) or
`Section.Type3.of.Givens` (right.right). When `Type2 = Type3` both targets coincide, nest
under the outer right conjunct: `.snd.fst` / `.snd.snd` (not a flat `.fst` / `.snd`).
-/
def Name.andRightProjName (moduleTokens : List String) (declName : Name) (left : Bool) : Name :=
  let leftTokens := moduleTokens.andRightLeftTokens
  let rightTokens := moduleTokens.andRightRightTokens
  let base := (if left then leftTokens else rightTokens).foldl Name.str default
  let base :=
    if leftTokens == rightTokens then
      (base.str "snd").str (if left then "fst" else "snd")
    else
      base
  base.lemmaName declName

/--
Generated declaration name for an `mp.left` / `mp.right` projection.

Applies the `mp` transformation to the source tokens (replacing `is` with `of`),
then drops the appropriate conjunct type. Mirrors `Name.andProjName` for the
`Type1.is.Type2.Type3` biconditional shape.
-/
def Name.mpProjName (moduleTokens : List String) (declName : Name) (left : Bool) : Name :=
  let leftTokens := moduleTokens.mpProjTokens true
  let rightTokens := moduleTokens.mpProjTokens false
  let base := (if left then leftTokens else rightTokens).foldl Name.str default
  let base :=
    if leftTokens == rightTokens then
      base.str (if left then "fst" else "snd")
    else
      base
  base.lemmaName declName


def Expr.subst (type value : Expr) (subst : Expr → Expr) (parity : ℕ) : Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let binders := (binders.zipParity parity).map fun ⟨comm, binderName, binderType, binderInfo⟩ =>
    (binderName, if comm then subst binderType else binderType, binderInfo)
  let telescope := fun lam body =>
    binders.foldl
      (fun body ⟨binderName, binderType, binderInfo⟩ =>
        lam binderName binderType body binderInfo
      )
      body
  (subst type, value.mkApp ((List.range binders.length).map fun i => (.bvar i)).reverse).map (telescope Expr.forallE) (telescope .lam)


def Expr.substNat (type value : Expr) (lit : Nat := 1) : MetaM (Expr × Expr) := do
  forallTelescope type fun args body => do
    let some (_, _, oneExpr) := body.findOfNatLit lit |
      throwError "subst: no OfNat literal {lit} found in the theorem type"
    let oneType ← inferType oneExpr
    withLocalDecl `n BinderInfo.implicit oneType fun n => do
      let body' :=
        if lit == 1 && (body.findOfNatLitInConstArg lit `List.Vector.repeat).isSome then
          body.replaceOfNatLitInConstArg lit `List.Vector.repeat n
            |>.replaceOfNatLitAsHMulLefts lit n
        else if lit == 1 && (body.findOfNatLitInConstArg lit `Tensor.repeat).isSome then
          body.replaceOfNatLitInConstArg lit `Tensor.repeat n
            |>.replaceOfNatLitAsHMulLefts lit n
        else if oneType.isNumericType then
          body.replaceAllExpr n oneExpr
        else
          body.replaceExpr n oneExpr |>.1
      let ⟨binders, _⟩ := type.decompose_forallE
      let insertIdx :=
        binders.map (·.2.2) |>.reverse |>.findIdx? (· == .default) |>.getD args.size
      let oneExpr' ← instantiateMVars oneExpr
      let u ← getLevel oneType
      let hType := mkAppN (mkConst ``Eq [u]) #[oneType, n, oneExpr']
      withLocalDecl `h BinderInfo.default hType fun h => do
        let motive ← mkLambdaFVars #[n] body'
        let pr := value.mkApp args.toList
        let symm := mkAppN (mkConst ``Eq.symm [u]) #[oneType, n, oneExpr', h]
        let proofBody := mkAppN (mkConst ``Eq.subst [u]) #[oneType, motive, oneExpr', n, symm, pr]
        let before := args.take insertIdx
        let after := args.drop insertIdx
        let allArgs := before.push n |>.push h |>.append after
        let type' ← mkForallFVars allArgs body'
        let value' ← mkLambdaFVars allArgs proofBody
        return (← instantiateMVars type', ← instantiateMVars value')


/--
Drop the plural `S` after removing an `SEq` prefix.
Matches `([A-Z][a-z]+)S(?![a-z])` — e.g. `PermuteS__Neg` → `Permute__Neg`, but `PermuteSign` unchanged.
-/
partial def List.dropSEqPluralS (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | c :: cs' =>
    if c.isUpper then
      let lowers := cs'.takeWhile (·.isLower)
      if lowers.isEmpty then
        cs
      else
        let rest := cs'.drop lowers.length
        let dropPluralS :=
          match rest with
          | 'S' :: rest' =>
            match rest' with
            | [] => true
            | c' :: _ => !c'.isLower
          | _ => false
        if dropPluralS then
          c :: lowers ++ rest.drop 1
        else
          cs
    else
      cs

def List.castPath (list : List String) (comm : Bool) : List String :=
  match list.findIdx? (· == "as") with
  | some i =>
    let ⟨before, rest⟩ := list.splitAt i
    match rest with
    | _ :: fileName :: tail =>
      if comm then
        before ++ ["eq", "Cast_" ++ fileName] ++ tail
      else
        before.dropLast ++ ["Cast_" ++ before.getLast!, "eq", fileName] ++ tail
    | _ =>
      panic! s!"cast attribute requires an `as` segment followed by a file name, got: {list}"
  | none =>
    let first := list[1]!
    if first.startsWith "SEq" then
      let first := String.ofList ((first.drop 3).chars.toList.dropSEqPluralS)
      list[0]! :: first :: ["eq", "Cast"] ++ list.drop 2
    else
      panic! s!"cast attribute requires module path to contain `SEq/as`, got: {list}"

def Expr.cast.extract: Expr → List Level × Expr × Expr × Expr × Expr × Expr × Expr
  | .app (.app (.app (.app (.app (.app (.const `SEq us) α) Vector) n) m) a) b => (us, α, Vector, n, m, a, b)
  | type => panic! s!"Expected an operator of SEq, but got {type.ctorName} :\n{type}"

def Expr.cast.type (deBruijn : Nat) (type value : Expr) (comm : Bool := false) : Expr :=
  let (us, α, Vector, n, m, a, b) := Expr.cast.extract type
  let (u, v) :=
    match us with
    | [u, v] => (u, v)
    | _ => panic! s!"Expected exactly two universe levels in SEq, but got {us}"
  let hn := (Expr.const `Eq [u.succ]).mkApp [α, n, m]
  let heq := (Expr.const `HEq [v]).mkApp [Vector.mkApp [n], a, Vector.mkApp [m], b]
  let hn := (Expr.const `And.left []).mkApp [hn, heq, if deBruijn == 0 then value else value.incDeBruijnIndex deBruijn]
  let hn :=
    if comm then
      (Expr.const `Eq.symm [u.succ]).mkApp [α, n, m, hn]
    else
      hn
  let A := Vector.mkApp [n]
  let B := Vector.mkApp [m]
  let congrArg := (Expr.const `congrArg [u.succ, v.succ]).mkApp ([α, .sort v] ++ (if comm then [m, n] else [n, m]) ++ [Vector, hn])
  (Expr.const `Eq [v]).mkApp
    (if comm then
      [A, a, (Expr.const `cast [v]).mkApp [B, A, congrArg, b]]
    else
      [B, (Expr.const `cast [v]).mkApp [A, B, congrArg, a], b])

def Expr.cast.value (type : Expr) (comm : Bool := false) : Expr :=
  let (us, α, Vector, n, m, a, b) := Expr.cast.extract type
  (Expr.const (if comm then `SEq.cast.comm else `SEq.cast) us).mkApp [α, Vector, n, m, a, b]

def Expr.cast (type value : Expr) (parity : ℕ := 0) (comm : Bool := false) : List (Bool × Expr) × Expr × Expr :=
  let ⟨binders, type⟩ := type.decompose_forallE
  let value := value.mkApp ((List.range binders.length).map fun i => .bvar i).reverse
  let ⟨type, cast⟩ := type.decompose (Expr.cast.type (value := value) (comm := comm)) (Expr.cast.value (comm := comm))
  let binders := binders.zipParity parity
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
    (type, .app cast value).map
      (telescope (valueBinders.filterMap fun args@⟨_, _, deBruijn⟩ => if type.containsBVar deBruijn then some args else none) Expr.forallE)
      (telescope valueBinders .lam)
  )


