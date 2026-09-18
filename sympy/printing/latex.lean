import stdlib.Lean.Level
import stdlib.Lean.Name
import stdlib.List
import sympy.core.expr
open Lean (Name)
set_option linter.unusedVariables false

/--
| index |   hex  | color|
| ----- | ------ | -----|
| 0     |"#999"| Gray |
| 1     |"#99f"| Blue |
| 2     |"#9f9"|Green |
| 3     |"#9ff"| Cyan |
| 4     |"#f99"| Red  |
| 5     |"#f9f"| Pink |
| 6     |"#ff9"|Yellow|
| 7     |"#fff"|White |
-/
def Nat.toColor (n : ℕ) (ignore : Bool) : String :=
  if ignore then
    "%s"
  else
    let n := (n + 1) &&& 7
    let b := ['9', 'f'][n &&& 1]!
    let n := n >>> 1
    let g := ['9', 'f'][n &&& 1]!
    let n := n >>> 1
    let r := ['9', 'f'][n &&& 1]!
    -- for katex
    -- s!"\\colorbox\u007b#{r}{g}{b}\u007d\u007b$\\left(%s\\right)$\u007d"
    -- for complex math
    s!"\\colorbox\u007b#{r}{g}{b}\u007d\u007b$\\mathord\u007b\\left(%s\\right)\u007d$\u007d"
    -- for mathjax
    -- s!"\\bbox[#{r}{g}{b}]\u007b\\left(%s\\right)\u007d"

def Expr.is_Div : Expr → Bool
  | Basic (.BinaryInfix ⟨op⟩) .. =>
    match op with
    | `Div.div
    | `HDiv.hDiv
    | `Rat.divInt =>
      true
    | _ =>
      false
  | _ => false

def Expr.peelLatexCoe : Expr → Expr
  | e@(Basic (.UnaryPrefix ⟨op⟩) [arg] _) =>
    match op with
    | `Nat.cast
    | `Int.cast
    | `Rat.cast
    | `Int.ofNat
    | `Complex.ofReal
    | `Hyperreal.ofReal
    | `Fin.val
    | `Subtype.val
    | `DFunLike.coe =>
      arg.peelLatexCoe
    | _ =>
      e
  | e =>
    e


def Expr.is_Mem : Expr → Bool
  | Basic (.BinaryInfix ⟨op⟩) args _ =>
    match op with
    | `Membership.mem
    | `List.Mem => args.length == 2
    | _ => false
  | _ => false


/-- True when `e` denotes a `Set` / `Finset` (so `≤` should render as `⊆`). -/
def Expr.is_SetLike : Expr → Bool
  | Symbol _ ty => is_SetType ty
  | Basic (.Special ⟨op⟩) .. =>
    match op with
    | `Insert.insert
    | `Singleton.singleton
    | `setOf => true
    | _ => false
  | Basic (.BinaryInfix ⟨op⟩) .. =>
    match op with
    | `Union.union
    | `Inter.inter
    | `SDiff.sdiff => true
    | _ => false
  | Basic (.ExprWithAttr attr) .. =>
    match attr.name with
    | `Set.Ioo
    | `Set.Ico
    | `Set.Iio
    | `Set.Icc
    | `Set.Iic
    | `Set.Ioc
    | `Set.Ici
    | `Set.Ioi
    | `Set.image
    | `Set.preimage
    | `Set.range
    | `Finset.range
    | `Finset.image
    | `Finset.Ioo
    | `Finset.Ico
    | `Finset.Iio
    | `Finset.Icc
    | `Finset.Iic
    | `Finset.Ioc
    | `Finset.Ici
    | `Finset.Ioi => true
    | .str `Set _
    | .str `Finset _ => true
    | .str _ "image"
    | .str _ "preimage" => true
    | _ => false
  | Basic (.UnaryPrefix ⟨`Finset.toSet⟩) .. => true
  | _ => false
where
  is_SetType : Expr → Bool
    | Basic (.ExprWithAttr (.Lean_typeclass `Set)) .. => true
    | Basic (.ExprWithAttr (.Lean_typeclass `Finset)) .. => true
    | _ => false


/-- Flatten a `++` chain, skipping `id`. -/
def Expr.flattenAppend : Expr → List Expr
  | Basic (.ExprWithAttr (.Lean_operatorname `id)) [e] _ =>
    e.flattenAppend
  | Basic (.BinaryInfix ⟨`HAppend.hAppend⟩) [l, r] _ =>
    l.flattenAppend ++ r.flattenAppend
  | e =>
    [e]

/-- `A.hstack B` → row `[A B]` (not a comma list). -/
def Expr.hstackBlocks : Expr → Option (List Expr)
  | Basic (.ExprWithAttr (.Lean_operatorname `id)) [e] _ =>
    e.hstackBlocks
  | Basic (.ExprWithAttr (.LeanMethod `Tensor.hstack _)) [a, b] _ =>
    some [a, b]
  | _ =>
    none

/-- `hstack` rows stacked with `++` → rectangular block cells. -/
def Expr.blockMatrixRows (e : Expr) : Option (List (List Expr)) :=
  match e.flattenAppend.mapM Expr.hstackBlocks with
  | some rows@(row0 :: rest) =>
    let cols := row0.length
    if cols ≥ 1 && rest.all (fun r => r.length == cols) then
      some rows
    else
      none
  | _ =>
    none

def Expr.is_BlockMatrix : Expr → Bool
  | Basic (.ExprWithAttr (.Lean_operatorname `id)) [e] _ =>
    e.is_BlockMatrix
  | e@(Basic (.BinaryInfix ⟨`HAppend.hAppend⟩) ..) =>
    e.blockMatrixRows != none
  | e@(Basic (.ExprWithAttr (.LeanMethod `Tensor.hstack _)) ..) =>
    e.blockMatrixRows != none
  | _ =>
    false

def Expr.bmatrixFormat (nrows ncols : Nat) : String :=
  let row := " & ".intercalate (["%s"].repeat ncols)
  "\\begin{bmatrix} " ++ " \\\\ ".intercalate ([row].repeat nrows) ++ " \\end{bmatrix}"

def Expr.is_EnclosedGroup : Expr → Bool
  | Basic (.Special ⟨op⟩) args _ =>
    match op with
    | `Bool.toNat
    | `Finset.card
    | `abs
    | `Norm.norm
    | `Int.ceil
    | `Int.floor =>
      args.length == 1
    | _ =>
      false
  | Basic (.UnaryPrefix ⟨op⟩) args _ =>
    match op with
    | `Real.sqrt
    | `Root.sqrt
    | `Root.cubic
    | `Root.quartic =>
      args.length == 1
    | _ =>
      false
  | e =>
    e.is_BlockMatrix

def Expr.is_GetElem : Expr → Bool
  | Basic (.Special ⟨`GetElem.getElem⟩) args _ => args.length == 3
  | Basic (.Special ⟨op⟩) args _ =>
    match op with
    | `List.get
    | `List.Vector.get
    | `Tensor.get =>
      args.length == 2
    | _ =>
      false
  | _ => false

def Expr.is_GetElem? : Expr → Bool
  | Basic (.Special ⟨`GetElem?.getElem?⟩) args _ => args.length == 2
  | _ => false

/--
Peel consecutive `GetElem` / `*.get` applications into `(base, indices)`.
Used so `M[i][j]` becomes `{M}_{i j}` (one subscript level) instead of `{{M}_{i}}_{j}`.
-/
def Expr.collectGetElemChain : Expr → Expr × List Expr
  | e@(Basic (.Special ⟨op⟩) args _) =>
    match op, args with
    | `GetElem.getElem, xs :: i :: _ :: _ =>
      let (base, idxs) := xs.collectGetElemChain
      (base, idxs ++ [i])
    | `List.get, xs :: i :: _
    | `List.Vector.get, xs :: i :: _
    | `Tensor.get, xs :: i :: _ =>
      let (base, idxs) := xs.collectGetElemChain
      (base, idxs ++ [i])
    | _, _ =>
      (e, [])
  | e =>
    (e, [])

def Expr.is_LeanProperty : Expr → Bool
  | Basic (.ExprWithAttr (.LeanProperty name)) .. => name != `IsConstant.is_constant
  | _ => false

def Expr.is_Eye : Expr → Bool
  | Basic (.ExprWithAttr (.Lean_operatorname `id)) [e] _ => e.is_Eye
  | Basic (.ExprWithAttr (.Lean_operatorname `Tensor.eye)) .. => true
  | _ => false

def Expr.toList : Expr → Option (List Expr)
  | Basic (.BinaryInfix ⟨`List.cons⟩) [head, tail] _ =>
    if let some args := tail.toList then
      head :: args
    else
      none
  | .const (.ident `List.nil) => some .nil
  | _ => none

def Expr.toFinset : Expr → Option (List Expr)
  | Basic (.Special ⟨`Insert.insert⟩) [head, tail] _ =>
    if let some args := tail.toFinset then
      head :: args
    else
      none
  | e =>
    if let some x := e.asSingleton? then
      some [x]
    else
      none

def Expr.traceCases (e : Expr) : ℕ × Expr :=
  match e with
  | Basic (.Special ⟨`ite⟩) args _ =>
    match args with
    | [_, _, elseBranch] =>
      let ⟨n, e⟩ := elseBranch.traceCases
      ⟨n + 1, e⟩
    | _ =>
      ⟨1, e⟩
  | _ =>
    ⟨0, e⟩

/-- Render a bound/observed-value name for LaTeX.

The quoted name `«x.bvar»` denotes the observed value of the random variable
`x`; it renders as the bare *black* letter `x`, while the random variable `x`
itself is rendered red elsewhere. -/
def String.bvarLatex (s : String) : String :=
  if s.startsWith "«" && s.endsWith "»" then
    let inner := (s.drop 1).dropEnd 1 |>.copy
    if inner.endsWith ".bvar" then
      inner.dropEnd ".bvar".length |>.copy
    else s
  else s

/-- Name-level variant of `String.bvarLatex`; non-`.bvar` names use `escape_specials`. -/
def Lean.Name.bvarLatex (name : Name) (sep : String) : String :=
  let s := name.toString
  if s.startsWith "«" && s.endsWith "»" then
    s.bvarLatex
  else
    name.escape_specials sep

def Expr.asStack? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithAttr (.Lean_operatorname `Stack)) [n, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default binderName _ nil] _] _ =>
    some (binderName.bvarLatex "\\ ", n, fn)
  | _ =>
    none

/-- `Tensor.matProd n (fun i => body)` → `(i, n, body)`. -/
def Expr.asMatProd? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithAttr (.Lean_operatorname `Tensor.matProd)) [n, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default binderName _ nil] _] _ =>
    some (binderName.bvarLatex "\\ ", n, fn)
  | _ =>
    none

/-- Whether a node is a `volume` measure constant (e.g. `MeasureTheory.MeasureSpace.volume`). -/
def Expr.isVolume : Expr → Bool
  | const (.ident name) => name.toString.endsWith "volume"
  | Basic (.ExprWithAttr op) _ _ =>
    match op with
    | .Lean_function name
    | .Lean_operatorname name
    | .Lean_typeclass name
    | .LeanLemma name
    | .LeanMethod name _
    | .LeanProperty name => name.toString.endsWith "volume"
  | _ => false

/-- `intervalIntegral (fun i => body) a b μ` → `(i, a, b, body, μ)`. -/
def Expr.asIntervalIntegral? : Expr → Option (String × Expr × Expr × Expr × Expr)
  | Basic (.ExprWithAttr (.Lean_operatorname `intervalIntegral))
      [Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default binderName _ nil] _, a, b, μ] _ =>
    some (binderName.bvarLatex "\\ ", a, b, fn, μ)
  | _ =>
    none

/-- Read final name segment from any `.Lean_function`/`.Lean_operatorname`/`.Lean_typeclass`/`.LeanLemma`/`.LeanProperty`/`.LeanMethod` attr. -/
def Expr.getAttrNameSuffix : Expr → Option String
  | Basic (.ExprWithAttr (.Lean_function name)) _ _
  | Basic (.ExprWithAttr (.Lean_operatorname name)) _ _
  | Basic (.ExprWithAttr (.Lean_typeclass name)) _ _
  | Basic (.ExprWithAttr (.LeanLemma name)) _ _
  | Basic (.ExprWithAttr (.LeanProperty name)) _ _
  | Basic (.ExprWithAttr (.LeanMethod name _)) _ _ =>
    let s := name.toString
    some ((s.splitOn ".").getLastD s)
  | Basic (.Special ⟨op⟩) _ _ => some op.toString
  | _ => none

/-- Look up a named application where the name suffix matches `suffix`. -/
def Expr.isNamedApp (suffix : String) (e : Expr) : Bool :=
  match e.getAttrNameSuffix with
  | some name => name == suffix || name.endsWith suffix
  | none => false

/-- Inspect the args of an ExprWithAttr named application, returning (nameSuffix, args). -/
def Expr.asNamedApp? (e : Expr) : Option (String × List Expr) :=
  match e with
  | Basic (.ExprWithAttr attr) args _ =>
    let name : String :=
      match attr with
      | .Lean_function n | .Lean_operatorname n | .Lean_typeclass n
      | .LeanLemma n | .LeanProperty n => n.toString
      | .LeanMethod n _ => n.toString
    some ((name.splitOn ".").getLastD name, args)
  | _ => none

/-- `lintegral μ (fun x ↦ body)` → `(x, body, μ)`. -/
def Expr.asLintegral? : Expr → Option (String × Expr × Expr)
  | e =>
    if let some ("lintegral", args) := e.asNamedApp? then
      let lambdaArg : Option Expr := args.findSome? fun arg =>
        match arg with
        | Basic (.ExprWithLimits .Lean_lambda) .. => some arg
        | _ => none
      match lambdaArg with
      | some (Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default binderName _ nil] _) =>
        let rest := args.filter (fun a : Expr => !match a with | Basic (.ExprWithLimits .Lean_lambda) .. => true | _ => false)
        match rest with
        | [μ] => some (binderName.bvarLatex "\\ ", fn, μ)
        | _ => none
      | some (Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .instImplicit binderName _ nil] _) =>
        let rest := args.filter (fun a : Expr => !match a with | Basic (.ExprWithLimits .Lean_lambda) .. => true | _ => false)
        match rest with
        | [μ] => some (binderName.bvarLatex "\\ ", fn, μ)
        | _ => none
      | _ => none
    else none

/-- `integral μ (fun x ↦ body)` → `(x, body, μ)`.
Mirrors lean.js `Lean_int`: the measure is dropped from display and the
binder variable is shown after `∂` (or `d` for `volume`). -/
def Expr.asIntegral? : Expr → Option (String × Expr × Expr)
  | e =>
    if let some ("integral", args) := e.asNamedApp? then
      let lambdaArg : Option Expr := args.findSome? fun arg =>
        match arg with
        | Basic (.ExprWithLimits .Lean_lambda) .. => some arg
        | _ => none
      match lambdaArg with
      | some (Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default binderName _ nil] _) =>
        let rest := args.filter (fun a : Expr => !match a with | Basic (.ExprWithLimits .Lean_lambda) .. => true | _ => false)
        match rest with
        | [μ] => some (binderName.bvarLatex "\\ ", fn, μ)
        | _ => none
      | some (Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .instImplicit binderName _ nil] _) =>
        let rest := args.filter (fun a : Expr => !match a with | Basic (.ExprWithLimits .Lean_lambda) .. => true | _ => false)
        match rest with
        | [μ] => some (binderName.bvarLatex "\\ ", fn, μ)
        | _ => none
      | _ => none
    else none

/-- See through `Prod.fst ⟨a, b⟩` / `Prod.snd ⟨a, b⟩` to the component `a` / `b`. -/
def Expr.asPairProj? : Expr → Option Expr
  | e =>
    let isFst := e.isNamedApp "fst"
    if isFst || e.isNamedApp "snd" then
      match e with
      | Basic _ [inner] _ =>
        if inner.isNamedApp "mk" then
          match inner, isFst with
          | Basic _ [a, _] .., true => some a
          | Basic _ [_, b] .., false => some b
          | _, _ => none
        else none
      | _ => none
    else none

/-- `JointRandomSymbol x y` → `(x, y)`. -/
def Expr.asJointRandomSymbol? : Expr → Option (Expr × Expr)
  | e =>
    if let some ("JointRandomSymbol", args) := e.asNamedApp? then
      match args with
      | [x, y] => some (x.asPairProj?.getD x, y.asPairProj?.getD y)
      | _ => none
    else none

/-- Check if an Expr is a bound observation — either a single `«x.bvar»`
or a pair `(«x.bvar», «y.bvar»)`. Only such nodes may be elided from
`𝕡.prob …` / `𝕡.condProb …`. Mirrors lean.js `isBoundObservation`. -/
def Expr.isBoundObservation : Expr → Bool
  | Symbol name _ =>
    let s := name.toString
    s.startsWith "«" && s.endsWith "»" && s.contains ".bvar"
  | Basic (.Special ⟨.str _ "mk"⟩) [a, b] _ =>
    a.isBoundObservation && b.isBoundObservation
  | Basic (.Special ⟨`Singleton.singleton⟩) [x] _
  | Basic (.Special ⟨`Insert.insert⟩) [x] _ =>
    x.isBoundObservation
  | _ => false

/-- Unwrap `Basic (.Special ⟨.anonymous⟩) [𝕡.prob rv, pt]` — the method result
applied to a point — returning `("prob", [𝕡, rv, pt])`. -/
def Expr.asProbApp? : Expr → Option (String × List Expr)
  | Basic (.Special ⟨.anonymous⟩) [inner, pt] _ =>
    if let some ("prob", base :: rest) := inner.asNamedApp? then
      some ("prob", base :: rest ++ [pt])
    else none
  | _ => none

-- `𝕡.prob f₁ … fₙ pt` → `(𝕡, [f₁ … fₙ₋₁])`: the `.prob` accessor and the
-- observed value (last argument) are dropped, mirroring the lean.js
-- `probDensityParts` convention (`𝕡.prob (x, y) («x.bvar», «y.bvar»)` → `𝕡 (x, y)`).
-- The observation point is dropped only when it is a bound observation
-- (`«x.bvar»` or `(«x.bvar», «y.bvar»)`); otherwise no simplification occurs.
def Expr.asProb? : Expr → Option (Expr × List Expr)
  | e =>
    -- Direct match: `𝕡.prob rv` (method call without extra application)
    if let some ("prob", base :: rest) := e.asNamedApp? then
      match rest with
      | [] => none
      | [_] => some (base, rest)
      | _ =>
        if rest.getLast!.isBoundObservation then
          some (base, rest.take (rest.length - 1))
        else
          none
    -- Nested match: `(𝕡.prob rv) pt` (method result applied to a point)
    else if let some ("prob", base :: rest) := e.asProbApp? then
      match rest with
      | [] => none
      | _ =>
        if rest.getLast!.isBoundObservation then
          some (base, rest.take (rest.length - 1))
        else
          none
    else none

/-- `tsum (fun a ↦ body) (SummationFilter.unconditional α)` → `(a, α, body)`:
extract the binder name, domain type, and body from a `tsum` expression.
Mirrors lean.js `∑' «a.bvar» : α, f «a.bvar»` rendering. -/
def Expr.asTsum? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithLimits .Lean_tsum) args _ =>
    match args with
    | [Basic (.ExprWithLimits .Lean_lambda) [body, Binder .default name type nil] _] =>
      -- No explicit summation filter; type comes from binder type
      some (name.toString.bvarLatex.escape_specials, type, body)
    | [Basic (.ExprWithLimits .Lean_lambda) [body, Binder .default name type nil] _, _filter] =>
      -- Filter present; type still from binder
      some (name.toString.bvarLatex.escape_specials, type, body)
    | _ => none
  | _ => none

/-- Extract the last name segment from any ExprWithAttr or ExprWithLimits. -/
def Expr.getAttrNameSuffix? : Expr → Option String
  | Basic (.ExprWithAttr (.LeanProperty name)) _ _
  | Basic (.ExprWithAttr (.Lean_function name)) _ _
  | Basic (.ExprWithAttr (.Lean_operatorname name)) _ _
  | Basic (.ExprWithAttr (.Lean_typeclass name)) _ _
  | Basic (.ExprWithAttr (.LeanLemma name)) _ _
  | Basic (.ExprWithAttr (.LeanMethod name _)) _ _ =>
    some (name.toString.splitOn "." |>.getLastD "")
  | Basic (.Special ⟨name⟩) _ _ =>
    let s := name.toString
    some ((s.splitOn ".").getLastD s)
  | _ => none

/-- Unwrap `Basic (.Special ⟨.anonymous⟩) [𝕡.map X, pt]` — the method
result applied to a point — returning `("map", [𝕡, X, pt])`.
Matches both LeanProperty `.map` and Lean_function/Lean_operatorname `Measure.map`,
by scanning args for anything with suffix "map". -/
def Expr.asMapApp? : Expr → Option (String × List Expr)
  | Basic (.Special ⟨.anonymous⟩) args _ =>
    args.findSome? fun arg =>
      match arg.getAttrNameSuffix? with
      | some "map" =>
        match arg with
        | Basic (.ExprWithAttr (.LeanProperty _)) propArgs _ =>
          let rest := args.erase arg
          if rest.length == 1 then some ("map", propArgs ++ rest) else none
        | Basic (.ExprWithAttr _) funcArgs _ =>
          let n := funcArgs.length
          if n >= 2 then
            let μ := funcArgs[n - 1]!
            let rv := funcArgs.take (n - 1)
            let rest := args.erase arg
            if rest.length == 1 then
              some ("map", μ :: rv ++ rest)
            else none
          else none
        | _ => none
      | _ => none
  | _ => none

/-- Wrap a `Symbol`'s type in `RandomVariable` so `isRandomVariable` returns true
and it renders red. Mirrors the JS `Measure.map` special case in
`markRandomVarNames` which marks the map argument as a random variable
regardless of whether `IsProbabilityMeasure` is present. -/
def Expr.markAsRandomVariable : Expr → Expr
  | Symbol name type =>
    if type.isRandomVariable then Symbol name type
    else Symbol name (.Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [type] type.level)
  | e => e

/-- `𝕡.map X` or `Measure.map a 𝕡` → `(𝕡, [X])`: mirrors lean.js `mapLatexParts`.
Also handles `(𝕡.map X) {pt}` / `(Measure.map a 𝕡) {pt}` with singleton
observation point dropped when `pt` is a bound observation.

LeanProperty `.map` args are [𝕡, X] → return (𝕡, [X]).
Lean_function/Lean_operatorname `Measure.map a 𝕡` args are [a, 𝕡] → return (𝕡, [a]). -/
def Expr.asMapDirect? : Expr → Option (Expr × List Expr)
  | e =>
    match e.getAttrNameSuffix? with
    | some "map" =>
      match e with
      | Basic (.ExprWithAttr (.LeanProperty _)) args _ =>
        let n := args.length
        if n >= 3 then
          if args[n - 1]!.isBoundObservation then
            some (args[0]!, args.take (n - 1) |>.tail!)
          else none
        else if n >= 2 then
          some (args[0]!, args.tail!)
        else none
      | Basic (.ExprWithAttr _) args _ =>
        let n := args.length
        if n == 2 then
          some (args[1]!, [args[0]!])
        else if n >= 3 then
          some (args[1]!, args.take 1)
        else none
      | _ => none
    | _ => none

/-- `𝕡.map X` or `Measure.map a 𝕡` → `(𝕡, [X])`: mirrors lean.js `mapLatexParts`.
Also handles `(𝕡.map X) {pt}` / `(Measure.map a 𝕡) {pt}` with singleton
observation point dropped when `pt` is a bound observation.

LeanProperty `.map` args are [𝕡, X] → return (𝕡, [X]).
Lean_function/Lean_operatorname `Measure.map a 𝕡` args are [a, 𝕡] → return (𝕡, [a]).
DFunLike.coe wrapping: (`map_expr`) `{pt}` → fold if pt is bound observation. -/
def Expr.asMap? : Expr → Option (Expr × List Expr)
  | Basic (.ExprWithAttr (.Lean_operatorname `DFunLike.coe)) [F, a] _ =>
    if a.isBoundObservation then
      F.asMapDirect?.map (fun (obj, fns) => (obj, fns.map markAsRandomVariable))
    else none
  | e =>
    match e.asMapDirect? with
    | some (obj, fns) => some (obj, fns.map markAsRandomVariable)
    | none =>
      if let some ("map", args) := e.asMapApp? then
        match args with
        | base :: rest =>
          if rest.length ≥ 2 then
            some (base, (rest.take (rest.length - 1)).map markAsRandomVariable)
          else none
        | _ => none
      else none

/-- How an `Expectation` term is displayed.
- `map f rv`: `Expectation (𝕡.map rv) f` → `𝔼_rv(f(rv))`
- `cond f x y`: `Expectation (μ.withDensity (fun a ↦ 𝕡.condProb (x, y) (a, b))) f`
  → `𝔼_x(f(x) | y)`. -/
inductive ExpectationView where
  | map (f rv : Expr)
  | cond (f x y : Expr)

/-- Decompose an `Expectation` term into either the pushforward (`map`) or
conditional-density (`cond`) view, mirroring lean.js `expectationLatexParts`. -/
def Expr.asExpectation? : Expr → Option ExpectationView
  | e =>
    if let some ("Expectation", [nu, f]) := e.asNamedApp? then
      -- `Expectation (𝕡.map rv) f` → 𝔼_rv(f(rv))
      if let some (_obj, rv :: _) := nu.asMap? then
        some (.map f rv)
      -- `Expectation (μ.withDensity (fun a ↦ 𝕡.condProb (x, y) (a, b))) f`
      else if let some ("withDensity",
            [_μ, Basic (.ExprWithLimits .Lean_lambda)
              [body, Binder .default binderName _ nil] _]) := nu.asNamedApp? then
        if let some ("condProb", _𝕡 :: joint :: point :: _) := body.asNamedApp? then
          if let some (x, y) := joint.asJointRandomSymbol? then
            -- observation point must be `(«a.bvar», …)` whose first component
            -- is the lambda's bound variable (mirrors the JS binder check)
            if let Basic (.Special ⟨.str _ "mk"⟩) [Symbol ptX _, _] _ := point then
              if ptX == binderName then
                some (.cond f (markAsRandomVariable x) (markAsRandomVariable y))
              else none
            else none
          else none
        else none
      else none
    else none

/-- Unwrap `Basic (.Special ⟨.anonymous⟩) [𝕡.condProb rv, pt]` — the method
result applied to a point — returning `("condProb", [𝕡, rv, pt])`. -/
def Expr.asCondProbApp? : Expr → Option (String × List Expr)
  | Basic (.Special ⟨.anonymous⟩) [inner, pt] _ =>
    if let some ("condProb", base :: rest) := inner.asNamedApp? then
      some ("condProb", base :: rest ++ [pt])
    else none
  | _ => none

/-- `𝕡.condProb (x, y) pt` → `(𝕡, x, y)`: mirrors lean.js `condProbParts`.
The observation point `pt` is dropped (as in `asProb?`), and the single
surviving random-variable pair is required to be a two-component pair so it can
render as `(x | y)`. -/
def Expr.asCondProb? : Expr → Option (Expr × Expr × Expr)
  | e =>
    if let some ("condProb", base :: rest) := e.asNamedApp? then
      match rest with
      | [pair] =>
        match pair.asJointRandomSymbol? with
        | some (x, y) => some (base, x, y)
        | none => none
      | [pair, point] =>
        if point.isBoundObservation then
          match pair.asJointRandomSymbol? with
          | some (x, y) => some (base, x, y)
          | none => none
        else
          none
      | _ => none
    else if let some ("condProb", base :: rest) := e.asCondProbApp? then
      match rest with
      | [pair, point] =>
        if point.isBoundObservation then
          match pair.asJointRandomSymbol? with
          | some (x, y) => some (base, x, y)
          | none => none
        else
          none
      | _ => none
    else none

/-- Check if an Expr is of form `ae μ`. -/
def Expr.isAeMeasure (e : Expr) : Bool :=
  match e.asNamedApp? with
  | some ("ae", _) => true
  | _ => false

/-- `EventuallyEq (ae μ) f g` → `(f, g)` — the filter is dropped, matching the
lean.js `LeanMEq` rendering `f =^{m} g` for the source notation `f =ᵐ[μ] g`. -/
def Expr.asEventuallyEq? : Expr → Option (Expr × Expr)
  | e =>
    if let some ("EventuallyEq", [μ, f, g]) := e.asNamedApp? then
      if μ.isAeMeasure then some (f, g) else none
    else none

/-- `Prod.mk (Prod.fst p) (Prod.snd p)` — an eta-expanded pair function — renders
like the source-level pair: `(a, b)` when `p = Prod.mk a b` literally, else
`p.fst, p.snd`. -/
def Expr.asEtaPair? : Expr → Option (List Expr)
  | e =>
    if let some ("mk", [p1, p2]) := e.asNamedApp? then
      match p1.asNamedApp?, p2.asNamedApp? with
      | some ("fst", [inner]), some ("snd", [p2']) =>
        match inner.asNamedApp? with
        | some ("mk", [a, b]) => some [a, b]
        | _ => some [inner, p2']
      | _, _ => none
    else none

/-- `Eventually (fun y ↦ body) (ae μ)` → `(y, body, μ)`. -/
def Expr.asEventuallyAe? : Expr → Option (String × Expr × Expr)
  | e =>
    if let some ("Eventually", args) := e.asNamedApp? then
      match args with
      | [lambdaArg, aeApp] =>
        if aeApp.isAeMeasure then
          match lambdaArg with
          | Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default binderName _ nil] _ =>
            match aeApp with
            | Basic (.ExprWithAttr _) [μ] _ =>
              some (binderName.bvarLatex "\\ ", fn, μ)
            | _ => none
          | _ => none
        else none
      | _ => none
    else none

def LimTo.latex : LimTo → String
  | inf => "\\infty"
  | ninf => "-\\infty"
  | nhds _ | nhdsPos _ | nhdsNeg _ => ""

def Expr.asArchimedeanMk? : Expr → Option Expr
  | Basic (.Special ⟨`ArchimedeanClass.mk⟩) (x :: _) _ => some x
  | _ => none

def Expr.asLtNatZero? : Expr → Option Expr
  | Basic (.BinaryInfix ⟨`LT.lt⟩) [const (.natVal 0), x] _ => some x
  | _ => none

def Expr.asNatZeroLt? : Expr → Option Expr
  | Basic (.BinaryInfix ⟨`LT.lt⟩) [x, const (.natVal 0)] _ => some x
  | _ => none

def Expr.asTendsToZero? : Expr → Option Expr
  | Basic (.BinaryInfix ⟨`LT.lt⟩) [left, right] _ =>
    if left.isNatZero then
      right.asArchimedeanMk?
    else
      none
  | _ => none

def Expr.asTendsToInf? : Expr → Option Expr
  | Basic (.BinaryInfix ⟨`LT.lt⟩) [left, right] _ =>
    if right.isNatZero then
      left.asArchimedeanMk?
    else
      none
  | _ => none

def Expr.asTendsToPosInf? : Expr → Option Expr
  | Basic (.BinaryInfix ⟨`And⟩) [l, r] _ =>
    match l.asLtNatZero?, r.asTendsToInf? with
    | some x, some y => if x == y then some x else none
    | _, _ => none
  | _ => none

def Expr.asTendsToNegInf? : Expr → Option Expr
  | Basic (.BinaryInfix ⟨`And⟩) [l, r] _ =>
    match l.asNatZeroLt?, r.asTendsToInf? with
    | some x, some y => if x == y then some x else none
    | _, _ => none
  | _ => none

def Expr.asTendsToZeroPos? : Expr → Option Expr
  | Basic (.BinaryInfix ⟨`And⟩) [l, r] _ =>
    match l.asLtNatZero?, r.asTendsToZero? with
    | some x, some y => if x == y then some x else none
    | _, _ => none
  | _ => none

def Expr.asTendsToZeroNeg? : Expr → Option Expr
  | Basic (.BinaryInfix ⟨`And⟩) [l, r] _ =>
    match l.asNatZeroLt?, r.asTendsToZero? with
    | some x, some y => if x == y then some x else none
    | _, _ => none
  | _ => none

def Expr.tendsToLatexArg? : Expr → Option Expr
  | e =>
    e.asTendsToZero?
    <|> e.asTendsToInf?
    <|> e.asTendsToPosInf?
    <|> e.asTendsToNegInf?
    <|> e.asTendsToZeroPos?
    <|> e.asTendsToZeroNeg?

def Expr.methodFormat (obj : Expr) (args : List Expr) (func : Operator) (attr: String) (level : ℕ) : String :=
  let obj := level.toColor (obj.priority > func.priority || obj.toList != none || obj.is_Eye)
  let args := args.map fun arg =>
    level.toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
  let args := "\\ ".intercalate args
  if args.isEmpty then
    s!"{obj}.{attr}"
  else
    s!"{obj}.{attr}\\ {args}"

def BinaryInfix.latexFormat (op : BinaryInfix) (left right : Expr) (level : ℕ)
    (command : Option String := none) : String :=
  let func := op.func
  let opStr := command.getD func.command
  -- left associative operators
  let left := level.toColor (left.priority ≥ func.priority || left.is_EnclosedGroup)
  let right := level.toColor (right.priority > func.priority || right.is_Div || right.is_BlockMatrix)
  s!"{left} {opStr} {right}"


def Expr.latexFormat : Expr → String
  | nil => ""
  | const _
  | sort _
  | Symbol .. => "%s"

  | e@(Basic func args level) =>
    let opStr := func.command
    match func with
    | .BinaryInfix binop@(⟨op⟩) =>
      match args with
      | [left, right] =>
        match op with
        | `Div.div
        | `HDiv.hDiv
        | `Rat.divInt =>
          if left.is_Div then
            "\\left. %s \\right/ %s"
          else
            s!"{opStr} %s %s"

        | `FloorDiv =>
          "%s {/\\!\\!/} %s"

        | `HPow.hPow =>
          let left := level.toColor (left.priority ≥ func.priority || left.is_EnclosedGroup)
          s!"{left} {opStr} %s"
        | `LT.lt =>
          if e.asTendsToZero? != none then
            "%s \\to 0"
          else if e.asTendsToInf? != none then
            "%s \\to \\infty"
          else
            binop.latexFormat left right level
        | `LE.le =>
          -- `Set` / `Finset` use the lattice `≤`, which should display as `⊆`
          if left.is_SetLike || right.is_SetLike then
            binop.latexFormat left right level "\\subseteq"
          else
            binop.latexFormat left right level
        | `And =>
          if e.asTendsToPosInf? != none then
            "%s \\to +\\infty"
          else if e.asTendsToNegInf? != none then
            "%s \\to -\\infty"
          else if e.asTendsToZeroPos? != none then
            "%s \\to 0^{+}"
          else if e.asTendsToZeroNeg? != none then
            "%s \\to 0^{-}"
          else
            let left := level.toColor (left.priority > func.priority)
            let right := level.toColor (right.priority ≥ func.priority)
            s!"{left} {opStr} {right}"
        | `Or =>
          -- right associative operators
          let left := level.toColor (left.priority > func.priority)
          let right := level.toColor (right.priority ≥ func.priority)
          s!"{left} {opStr} {right}"
        | `List.cons =>
          if let some args := e.toList then
            let format := ", ".intercalate (["%s"].repeat args.length)
            s!"\\left[{format}\\right]"
          else
            binop.latexFormat left right level
        | `HAppend.hAppend =>
          if let some rows@(row0 :: _) := e.blockMatrixRows then
            Expr.bmatrixFormat rows.length row0.length
          else
            binop.latexFormat left right level
        | _ =>
          binop.latexFormat left right level
      | _ =>
        op.toString

    | .UnaryPrefix ⟨op⟩ =>
      if let [arg] := args then
        let format :=
          match op with
          | `Not =>
            if arg.asTendsToZero? != none then
              "\\lnot\\left({%s} \\to 0\\right)"
            else if arg.asTendsToInf? != none then
              "\\lnot\\left({%s} \\to \\infty\\right)"
            else if arg.asTendsToPosInf? != none then
              "\\lnot\\left({%s} \\to +\\infty\\right)"
            else if arg.asTendsToNegInf? != none then
              "\\lnot\\left({%s} \\to -\\infty\\right)"
            else if arg.asTendsToZeroPos? != none then
              "\\lnot\\left({%s} \\to 0^{+}\\right)"
            else if arg.asTendsToZeroNeg? != none then
              "\\lnot\\left({%s} \\to 0^{-}\\right)"
            else if arg.is_Mem then
              "%s \\notin %s"
            else
              ""
          | `Real.sqrt
          | `Root.sqrt
          | `Root.cubic
          | `Root.quartic =>
            s!"{opStr}%s"
          | `Complex.conj =>
            "\\overline{%s}"
          | `Neg.neg =>
            if let const (.ident `Hyperreal.epsilon) := arg then
              "0^-"
            else if arg.is_Div then
              s!"{opStr}%s"
            else
              ""
          | `DFunLike.coe =>
            ""  -- hide `coe` coercion; render just the underlying measure
          | _ =>
            ""
        if format.isEmpty then
          let arg := level.toColor (arg.priority ≥ func.priority || arg.is_EnclosedGroup)
          let arg :=
            if func.priority == 76 then
              "\\ " ++ arg
            else
              arg
          s!"{opStr}{arg}"
        else
          format
      else
        op.toString

    | .UnaryPostfix ⟨op⟩ =>
      if let [arg] := args then
        let arg := level.toColor (arg.priority ≥ func.priority || arg.is_EnclosedGroup)
        s!"{arg}{opStr}"
      else
        op.toString

    | .ExprWithLimits op =>
      let opStr' :=
        match op with
        | .Lean_forall =>
          match args with
          | [Symbol _ (sort (.succ _)), _] =>
            "%s \\rightarrow %s"
          | [_, Binder .given _ type nil] =>
            match type with
            | Basic (.BinaryInfix ⟨`Membership.mem⟩) .. => ""
            | _ => "%s \\rightarrow %s"
          | _ =>
            ""
        | .Lean_lambda =>
          opStr ++ "\\ %s".repeat (args.length - 1) ++ "\\mapsto\\ %s"
        | .Lean_let =>
          "{\\begin{align*}" ++ ("\\\\".intercalate ([s!"&{opStr}\\ %s := ⋯"].repeat (args.length - 1))) ++ "\\\\&%s\\end{align*}}"
        | .Lean_tsum =>
          if let some (name, type, body) := e.asTsum? then
            -- \mathop{\sum\nolimits'} puts ' atop ∑ (right-top corner),
            -- matching the imply's JS-templated format exactly.
            "\\mathop{\\sum\\nolimits'}\\limits_{\\substack{%s : %s}} {%s}"
          else
            opStr ++ "\\ %s".repeat (args.length - 1) ++ ",\\ %s"
        | .Lean_sum
        | .Lean_prod
        | .Lean_bigcup
        | .Lean_bigcap =>
          opStr ++ "\\limits_{\\substack{%s}} {%s}"
        | .Lean_lim =>
          match Expr.asLimBound? args with
          | some _ =>
            "\\lim\\limits_{%s \\to %s} {%s}"
          | none =>
            if args.length == 1 then "\\lim %s" else ""
        | _ =>
          ""
      if opStr' == "" then
        opStr ++ "\\ %s".repeat (args.length - 1) ++ ",\\ %s"
      else
        opStr'

    | .Special ⟨op⟩ =>
      match op with
      | .anonymous =>
        if let some (obj, fns) := e.asMap? then
          -- lean.js `mapLatexParts`: `(𝕡.map X) {pt}` → `𝕡 X`.
          let obj := level.toColor (obj.priority > func.priority || obj.toList != none || obj.is_Eye)
          let fns := fns.map fun arg =>
            (0 : Nat).toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
          "\\ ".intercalate (obj :: fns)
        else
          let args := args.zipIdx.map fun ⟨arg, i⟩ =>
            level.toColor ((i == 0 || arg.priority > func.priority) && (i > 0 || arg.priority ≥ func.priority) || arg.is_Div || arg.is_BlockMatrix)
          "\\ ".intercalate args
      | `ite =>
        let ⟨n, last⟩ := e.traceCases
        if last == .nil then
          "\\overbrace{\\begin{cases} %s \\end{cases}}^{\\color{blue}match}".format "\\\\".implode (["%s"].repeat n)
        else
          "\\begin{cases} %s \\\\ {%%s} & {\\color{blue}\\text{else}} \\end{cases}".format "\\\\".implode (["%s"].repeat n)
      | `Insert.insert =>
        if let some elems := e.toFinset then
          let format := ", ".intercalate (["%s"].repeat elems.length)
          "\\left\\{" ++ format ++ "\\right\\}"
        else
          "\\left\\{%s, %s\\right\\}"
      | `List.get
      | `List.Vector.get
      | `Tensor.get
      | `GetElem.getElem =>
        let (base, indices) := e.collectGetElemChain
        if indices.isEmpty then
          opStr
        else
          let baseFmt := level.toColor (base.priority > func.priority || base.is_EnclosedGroup || base.is_LeanProperty || base.is_Eye)
          baseFmt ++ "_{" ++ ", ".intercalate (["%s"].repeat indices.length) ++ "}"
      | `GetElem?.getElem? =>
        match args with
        | list :: _ =>
          let list := level.toColor (list.priority > func.priority || list.is_EnclosedGroup || list.is_GetElem || list.is_GetElem? || list.is_LeanProperty || list.is_Eye)
          let index := "{%s?}"
          s!"{list}_{index}"
        | _ =>
          opStr
      | .str `Prod "mk" =>
        let args := ["%s"].repeat args.length
        let args := ", ".intercalate args
        ((0 : Nat).toColor false).replaceFirst "%s" args
      | .str _ "mk" =>
        let args := ["%s"].repeat args.length
        let args := ", ".intercalate args
        s!"\\langle {args} \\rangle"
      | `OfNat.ofNat =>
        "\\mathbf{%s}_{%s}"
      | _ =>
        opStr
    | .ExprWithAttr op =>
      -- Pre-check foldings first (work for both Lean_function and Lean_operatorname)
      if let some (_binderName, _fn, μ) := e.asIntegral? then
        if μ.isVolume then
          "\\int {%s}\\, {\\color{blue}\\mathrm{d}}{%s}"
        else
          "\\int {%s}\\, {\\color{blue}\\partial}{%s}"
      else if let some (_binderName, _fn, _μ) := e.asLintegral? then
        "\\int^{⁻} {%s}\\, {\\color{blue}\\partial}{%s}"
      else if let some view := e.asExpectation? then
        match view with
        | .map _ _ =>
          "\\mathop{\\mathbb{E}}\\limits_{%s}\\left(%s\\left(%s\\right)\\right)"
        | .cond _ _ _ =>
          "\\mathop{\\mathbb{E}}\\limits_{%s}\\left(%s\\left(%s\\right)\\ \\mathrel{\\bigg|}\\ %s\\right)"
      else if let some (_, _) := e.asJointRandomSymbol? then
        "%s, %s"
      else if let some (_, _, _) := e.asEventuallyAe? then
        "\\forall^{ᵐ}\\,{%s}, {%s}"
      else if let some (obj, fns) := e.asProb? then
        let obj := level.toColor (obj.priority > func.priority || obj.toList != none || obj.is_Eye)
        let fns := fns.map fun arg =>
          (0 : Nat).toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
        "\\ ".intercalate (obj :: fns)
      else if let some (obj, fns) := e.asMap? then
        let obj := level.toColor (obj.priority > func.priority || obj.toList != none || obj.is_Eye)
        let fns := fns.map fun arg =>
          (0 : Nat).toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
        "\\ ".intercalate (obj :: fns)
      else if let some (obj, _, _) := e.asCondProb? then
        let obj := level.toColor (obj.priority > func.priority || obj.toList != none || obj.is_Eye)
        let pair := (level.toColor false).replaceFirst "%s" "%s\\,\\middle|\\,%s"
        "{" ++ obj ++ "}\\ " ++ pair
      else if let some (_, _) := e.asEventuallyEq? then
        "{%s} {=^{\\mathrm{m}}} {%s}"
      else if let some (_) := e.asEtaPair? then
        "%s, %s"
      else match op with
      | .Lean_function _ =>
        let args := args.map fun arg =>
          level.toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
        opStr ++ "\\ " ++ "\\ ".intercalate args
      | .Lean_operatorname name =>
        match name with
        | `DFunLike.coe =>
          match args with
          | [F, a] =>
            let f := level.toColor (F.priority ≥ func.priority || F.toList != none || F.is_Eye)
            let a := level.toColor (a.priority ≥ func.priority || a.is_EnclosedGroup)
            s!"{f} {a}"
          | [F] =>
            let f := level.toColor (F.priority ≥ func.priority || F.toList != none || F.is_Eye)
            f
          | _ =>
            let args := args.map fun arg =>
              level.toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
            opStr ++ "\\ " ++ "\\ ".intercalate args
        | `id =>
          if let some rows@(row0 :: _) := e.blockMatrixRows then
            Expr.bmatrixFormat rows.length row0.length
          else if args.isEmpty then opStr else "%s"
        | `Exp.exp
        | `Real.exp => "{\\color{RoyalBlue} e} ^ %s"
        | `Finset.Ioo
        | `Set.Ioo => "\\left(%s, %s\\right)"
        | `Finset.Ico
        | `Set.Ico => "\\left[%s, %s\\right)"
        | `Finset.Iio
        | `Set.Iio => "\\left(-\\infty, %s\\right]"
        | `Finset.Icc
        | `Set.Icc => "\\left[%s, %s\\right]"
        | `Finset.Iic
        | `Set.Iic => "\\left(-\\infty, %s\\right]"
        | `Finset.Ioc
        | `Set.Ioc => "\\left(%s, %s\\right]"
        | `Finset.Ici
        | `Set.Ici => "\\left[%s, \\infty\\right)"
        | `Finset.Ioi
        | `Set.Ioi => "\\left(%s, \\infty\\right)"
        | `Tensor.eye => "\\mathbb{I}"
        | `Tensor.matProd =>
          match Expr.asMatProd? e with
          | some _ =>
            "\\prod\\limits_{%s < %s} {%s}"
          | none =>
            let args := args.map fun arg =>
              level.toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
            opStr ++ "\\ " ++ "\\ ".intercalate args
        | `intervalIntegral =>
          match Expr.asIntervalIntegral? e with
          | some (_, _, _, _, μ) =>
            if μ.isVolume then
              "\\int\\limits_{%s}^{%s} {%s}\\,{\\color{blue}\\mathrm{d}}%s"
            else
              "\\int\\limits_{%s}^{%s} {%s}\\,\\partial\\!\\left(%s\\right)\\,{\\color{blue}\\mathrm{d}}%s"
          | none =>
            let args := args.map fun arg =>
              level.toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
            opStr ++ "\\ " ++ "\\ ".intercalate args
        | `Stack =>
          let arg := level.toColor (
            if let [_, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default _ _ nil] _] := args then
              fn.priority ≥ (⟨`List.cons⟩ : BinaryInfix).func.priority
            else
              true
          )
          s!"\\left[%s < %s\\right] {arg}"
        | `letFun => "{\\begin{align*}&{\\color{blue}let}\\ %s : %s := ⋯\\\\&%s\\end{align*}}"
        | `KroneckerDelta => "\\delta_{%s %s}"
        | `descFactorial
        | `Nat.descFactorial => "{%s}^{\\underline{%s}}"
        | `ascFactorial
        | `Nat.ascFactorial => "{%s}^{\\overline{%s}}"
        | `OfScientific.ofScientific => "%s%s.%s"
        | `Set.image
        | `Finset.image =>
          -- Mathlib: `f '' s` (text so KaTeX does not treat '' as double-prime)
          "{%s}\\mathrel{\\text{''}}{%s}"
        | `Set.preimage =>
          -- Mathlib: `f ⁻¹' s`
          "{%s}^{-1}'{%s}"
        | `Subtype =>
          let postOp :=
            match args with
            | [Basic (.ExprWithLimits .Lean_lambda) [Basic (.BinaryInfix ⟨`LT.lt⟩) [const (.natVal 0), Symbol binderName binderType] _, Binder .default binderName' binderType' nil] _] =>
              if binderName == binderName' && binderType == binderType' then
                "%s^{+}"
              else
                ""
            | [Basic (.ExprWithLimits .Lean_lambda) [Basic (.BinaryInfix ⟨`LT.lt⟩) [Symbol binderName binderType, const (.natVal 0)] _, Binder .default binderName' binderType' nil] _] =>
              if binderName == binderName' && binderType == binderType' then
                "%s^{-}"
              else
                ""
            | _ =>
              ""
          if postOp.isEmpty then
            let args := args.map fun arg =>
              level.toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
            opStr ++ "\\ " ++ "\\ ".intercalate args
          else
            postOp
        | _  =>
          let args := args.map fun arg =>
            level.toColor (arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix)
          opStr ++ "\\ " ++ "\\ ".intercalate args
      | .LeanMethod name idx =>
        let attr := name.getLast.toString.escape_specials
        match attr, args with
        | "ediv", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left := level.toColor (left.priority ≥ func.priority)
          let right := level.toColor (right.priority > func.priority)
          s!"{left} \\div {right}"
        | "fdiv", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left := level.toColor (left.priority ≥ func.priority)
          let right := level.toColor (right.priority > func.priority)
          s!"{left} /\\!\\!/ {right}"
        | "fmod", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left := level.toColor (left.priority > func.priority)
          let right := level.toColor (right.priority > func.priority)
          "%s {\\color{red}\\%%%%} %s".format left, right
        | "hstack", _ =>
          if let some rows@(row0 :: _) := e.blockMatrixRows then
            Expr.bmatrixFormat rows.length row0.length
          else
            opStr
        | "choose", [_, _] =>
          "\\binom{%s}{%s}"
        | "image", _ =>
          if args.length > idx then
            "{%s}\\mathrel{\\text{''}}{%s}"
          else
            opStr
        | "preimage", _ =>
          if args.length > idx then
            "{%s}^{-1}'{%s}"
          else
            opStr
        | "descFactorial", [_, _] =>
          "{%s}^{\\underline{%s}}"
        | "ascFactorial", [_, _] =>
          "{%s}^{\\overline{%s}}"
        | "getSlice", [_, Basic (.Special ⟨`Slice.mk⟩) [start, _, step] _] =>
          if let const (.natVal 1) := step then
            if let const (.natVal 0) := start then
              "{%s}_{:%s}"
            else
              "{%s}_{%s:%s}"
          else
            if let const (.natVal 0) := start then
              "{%s}_{:%s:%s}"
            else
              "{%s}_{%s:%s:%s}"
        | "sum", [X, dim]
        | "prod", [X, dim] =>
          if dim == const (.natVal 0) then
            match Expr.asStack? X with
            | some _ => "\\" ++ attr ++ "\\limits_{\\substack{%s}} {%s}"
            | none => X.methodFormat [dim] func attr level
          else
            X.methodFormat [dim] func attr level
        | _, args =>
          if args.length ≤ idx then
            let op := name.toString.escape_specials
            let args := args.map fun arg =>
              level.toColor (arg.priority ≥ func.priority || arg.is_Div || arg.is_BlockMatrix)
            let args := "\\ ".intercalate args
            s!"{op}\\ {args}"
          else if let obj :: args := args.swap 0 idx then
            obj.methodFormat args func attr level
          else
            opStr
      | .Lean_typeclass _ =>
        let args := args.map fun arg =>
          level.toColor (arg.priority > func.priority || arg.toList != none || arg.is_Div || arg.is_BlockMatrix)
        let args := "\\ ".intercalate args
        s!"{opStr}\\ {args}"
      | .LeanProperty name =>
        let attr := name.getLast.toString
        match name with
        | `Complex.exp =>
          "{\\color{RoyalBlue} e} ^ %s"
        | `Complex.cos
        | `Complex.sin
        | `Complex.log =>
          s!"\\{attr} %s"
        | `IsConstant.is_constant =>
          "%s\\ {\\color{blue}\\text{is}}\\ {constant}"
        | `Tensor.T =>
          "{%s}^{\\color{magenta} T}"
        | `Tensor.det
        | `Matrix.det =>
          "\\left|{%s}\\right|"
        | `Nat.factorial =>
          "{%s}!"
        | _ =>
          match args with
          | arg :: _ =>
            let arg := level.toColor (arg.priority ≥ func.priority || arg.toList != none || arg.is_Eye)
            s!"{arg}.{attr}"
          | .nil =>
            name.toString.escape_specials
      | .LeanLemma _ =>
        opStr


  | Binder binder binderName _ value =>
    let binderName := binderName.bvarLatex "\\ "
    match binder with
    | .instImplicit =>
      binder.func.command
    | .default =>
      if value == .nil then
        binder.func.command.replaceFirst "%s" binderName
      else
        s!"\\left({binderName} : %s := %s\\right)"
    | _ =>
      binder.func.command.replaceFirst "%s" binderName


partial def Expr.toLatex (e : Expr) : String :=
  e.latexFormat.printf (latexArgs e)
where
  latexArgs : Expr → List String
  | nil => []

  | const val =>
    [val.toLatex]

  | sort u =>
    [u.toString]

  | Symbol name type =>
    if type.isRandomVariable then
      ["{\\color{red} {" ++ name.bvarLatex "." ++ "}}"]
    else
      [name.bvarLatex "."]

  | e@(Basic func args _) =>
    match func with
    | .ExprWithLimits op =>
      let args' :=
        match op with
        | .Lean_forall =>
          match args with
          | [returnType@(Symbol _ (sort (.succ _))), Binder .default _ binderType nil]
          | [returnType, Binder .given _ binderType nil] =>
            [binderType.toLatex, returnType.toLatex]
          | [scope, Binder .default binderName binderType nil] =>
            [("%s : %s".format (binderName.bvarLatex "\\ "), binderType.toLatex), scope.toLatex]
          | _ =>
            []
        | .Lean_lambda =>
          match args with
          | expr :: limits =>
            let limits := limits.map fun arg =>
              match arg with
              | Binder .default name _ nil =>
                name.bvarLatex "\\ "
              | _ =>
                arg.toLatex
            limits.reverse ++ [expr.toLatex]
          | .nil =>
            []
        | .Lean_let =>
          args.reverse.map fun expr =>
            if let Binder _ name type _ := expr then
              "{%s : %s}".format name.toString.bvarLatex.escape_specials, type.toLatex
            else
              "{%s}".format expr.toLatex
        | .Lean_tsum =>
          match e.asTsum? with
          | some (name, type, body) =>
            [name, type.toLatex, body.toLatex]
          | none =>
            args.reverse.map (·.toLatex)
        | .Lean_exists
        | .Lean_sum
        | .Lean_prod
        | .Lean_bigcup
        | .Lean_bigcap =>
          match args with
          | [expr, Binder .default name (Basic (.ExprWithAttr (.Lean_typeclass `Fin)) [n] _) nil] =>
            [("{%s < %s}".format name.toString.bvarLatex.escape_specials, n.toLatex), expr.toLatex]
          | [expr, Binder .default name type nil] =>
            [("{%s : %s}".format name.toString.bvarLatex.escape_specials, type.toLatex), expr.toLatex]
          | _ =>
            []
        | .Lean_lim =>
          match Expr.asLimBound? args with
          | some (n, dir, fn) =>
            let bound :=
              match dir with
              | .nhds x => x.toLatex
              | .nhdsPos x => x.toLatex ++ "^{+}"
              | .nhdsNeg x => x.toLatex ++ "^{-}"
              | d => d.latex
            [n.bvarLatex "\\ ", bound, fn.toLatex]
          | none =>
            []
        | _ =>
          []
      if args' == [] then
        map args |>.reverse
      else
        args'
    | .Special ⟨op⟩ =>
      match op with
      | `Nat.ModEq =>
        match args with
        | [d, a, b] =>
          [a.toLatex, b.toLatex, d.toLatex]
        | _ =>
          map args
      | `List.get
      | `List.Vector.get
      | `Tensor.get
      | `GetElem.getElem =>
        let (base, indices) := e.collectGetElemChain
        if indices.isEmpty then
          map args
        else
          map (base :: indices)
      | `ite =>
        merge_ite e []
      | `Insert.insert =>
        if let some elems := e.toFinset then
          map elems
        else
          match args with
          | [a, .Symbol b _] =>
            [a.toLatex, "..." ++ b.toString]
          | _ =>
            map args
      | `Subtype.mk
      | `Fin.mk =>
        let a : Option Expr :=
          match args with
          | [a, Basic op ..] =>
            match op with
            | .ExprWithAttr _
            | .ExprWithLimits .Lean_let =>
              a
            | .UnaryPrefix op =>
              if op.func.priority == 76 then
                a
              else
                none
            | _ =>
              none
          | _ =>
            none
        if let some a := a then
          map [a] ++ ["\\cdots"]
        else
          map args
      | `OfNat.ofNat =>
        match args with
        | [const (.natVal n), shape] =>
          let dims :=
            if let some dims := shape.toList then
              ",".intercalate (dims.map fun d => d.toLatex)
            else
              "{%s}".format shape.toLatex
          [toString n, dims]
        | _ =>
          map args
      | .anonymous =>
        if let some (obj, fns) := e.asMap? then
          obj.toLatex :: fns.map (·.toLatex)
        else
          map args
      | _ =>
        map args
    | .BinaryInfix ⟨`Div.div⟩
    | .BinaryInfix ⟨`HDiv.hDiv⟩
    | .BinaryInfix ⟨`Rat.divInt⟩ =>
      match args with
      | [left, right] =>
        if right.is_Div then
          let leftTex := "{%s}".format left.toLatex
          let rightTex := "{%s}".format (flattenedDiv right)
          [leftTex, rightTex]
        else
          map args
      | _ =>
        map args
    | .BinaryInfix ⟨`Membership.mem⟩ =>
      map args |>.reverse
    | .BinaryInfix ⟨`LT.lt⟩ =>
      if let some x := e.tendsToLatexArg? then
        [x.toLatex]
      else
        map args
    | .BinaryInfix ⟨`And⟩ =>
      if let some x := e.tendsToLatexArg? then
        [x.toLatex]
      else
        map args
    | .BinaryInfix ⟨`List.cons⟩ =>
      if let some args := e.toList then
        map args
      else
        map args
    | .BinaryInfix ⟨`HAppend.hAppend⟩ =>
      if let some rows := e.blockMatrixRows then
        map rows.flatten
      else
        map args
    | .ExprWithAttr op =>
      -- Pre-check foldings first (work for both Lean_function and Lean_operatorname)
      if let some (binderName, fn, _μ) := e.asIntegral? then
        [fn.toLatex, binderName]
      else if let some (binderName, fn, _μ) := e.asLintegral? then
        [fn.toLatex, binderName]
      else if let some view := e.asExpectation? then
        match view with
        | .map f rv => [rv.toLatex, f.toLatex, rv.toLatex]
        | .cond f x y => [x.toLatex, f.toLatex, x.toLatex, y.toLatex]
      else if let some (x, y) := e.asJointRandomSymbol? then
        [x.toLatex, y.toLatex]
      else if let some (binderName, body, _μ) := e.asEventuallyAe? then
        [binderName, body.toLatex]
      else if let some (obj, fns) := e.asProb? then
        obj.toLatex :: fns.map (·.toLatex)
      else if let some (obj, fns) := e.asMap? then
        obj.toLatex :: fns.map (·.toLatex)
      else if let some (obj, x, y) := e.asCondProb? then
        [obj.toLatex, x.toLatex, y.toLatex]
      else if let some (f, g) := e.asEventuallyEq? then
        [f.toLatex, g.toLatex]
      else if let some etaArgs := e.asEtaPair? then
        etaArgs.map (·.toLatex)
      else
        match op with
        | .LeanMethod op idx =>
          match op with
          | .str _ "getSlice" =>
            if let [base, Basic (.Special ⟨`Slice.mk⟩) [start, stop, step] _] := args then
              if let const (.natVal 1) := step then
                if let const (.natVal 0) := start then
                  map [base, stop]
                else
                  map [base, start, stop]
              else
                if let const (.natVal 0) := start then
                  map [base, stop, step]
                else
                  map [base, start, stop, step]
            else
              map args
          | .str _ "image" =>
            -- `s.image f` → latex args in Mathlib order `f '' s`
            match args.swap 0 idx with
            | [s, f] => map [f, s]
            | swapped => map swapped
          | .str _ "preimage" =>
            match args.swap 0 idx with
            | [s, f] => map [f, s]
            | swapped => map swapped
          | .str _ "hstack" =>
            if let some rows := e.blockMatrixRows then
              map rows.flatten
            else
              map (args.swap 0 idx)
          | .str _ "sum"
          | .str _ "prod" =>
            match args.swap 0 idx with
            | [X, dim] =>
              if dim == const (.natVal 0) then
                match Expr.asStack? X with
                | some (i, n, fn) =>
                  [s!"{i} < {n.toLatex}", fn.toLatex]
                | none =>
                  map (args.swap 0 idx)
              else
                map (args.swap 0 idx)
            | swapped =>
              map swapped
          | _ =>
            map (args.swap 0 idx)
        | .Lean_operatorname `Stack =>
          if let [n, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default i _ nil] _] := args then
            i.bvarLatex "\\ " :: map [n, fn]
          else
            map args
        | .Lean_operatorname `Tensor.matProd =>
          match Expr.asMatProd? e with
          | some (i, n, fn) =>
            i :: map [n, fn]
          | none =>
            map args
        | .Lean_operatorname `intervalIntegral =>
          match Expr.asIntervalIntegral? e with
          | some (i, a, b, fn, μ) =>
            if μ.isVolume then
              map [a, b, fn] ++ [i]
            else
              map [a, b, fn, μ] ++ [i]
          | none =>
            map args
        | .Lean_operatorname `letFun =>
          if let [_, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder _ h hType _] _] := args then
            h.bvarLatex "\\ " :: map [hType, fn]
          else
            map args
        | .Lean_operatorname `cast =>
          match args with
          | [Basic func .., a] =>
            match func with
            | .ExprWithAttr _
            | .Special ⟨.anonymous⟩ =>
              "\\cdots" :: map [a]
            | _ =>
              map args
          | args =>
            map args
        | .Lean_operatorname `OfScientific.ofScientific =>
          if let [mantissa, exponentSign, decimalExponent] := args then
            let mantissa :=
              if let const (.natVal mantissa) := mantissa then
                mantissa
              else
                0
            let decimalExponent :=
              if let const (.natVal decimalExponent) := decimalExponent then
                decimalExponent
              else
                0
            let pow10 := 10 ^ decimalExponent
            let integer := toString (mantissa / pow10)
            let fraction := toString (mantissa % pow10)
            let sign :=
              if let const .true := exponentSign then
                ""
              else
                "-"
            [sign, integer, fraction]
          else
            map args
        | .Lean_operatorname `Subtype =>
          let args :=
            match args with
            -- consider special cases:
            | [Basic (.ExprWithLimits .Lean_lambda) [Basic (.BinaryInfix ⟨`LT.lt⟩) [const (.natVal 0), Symbol binderName binderType] _, Binder .default binderName' binderType' nil] _] =>
              -- ℝ⁺ = Subtype fun x : ℝ => 0 < x
              if binderName == binderName' && binderType == binderType' then
                [binderType]
              else
                args
            | [Basic (.ExprWithLimits .Lean_lambda) [Basic (.BinaryInfix ⟨`LT.lt⟩) [Symbol binderName binderType, const (.natVal 0)] _, Binder .default binderName' binderType' nil] _] =>
              -- ℝ⁻ = Subtype fun x : ℝ => x < 0
              if binderName == binderName' && binderType == binderType' then
                [binderType]
              else
                args
            | _ =>
              args
          map args
        | .Lean_typeclass `HEq =>
          match args with
          | [a, Basic (.ExprWithAttr _) ..] =>
            map [a] ++ ["\\cdots"]
          | args@([a, Basic (.UnaryPrefix op) ..]) =>
            if op.func.priority == 76 then
              map [a] ++ ["\\cdots"]
            else
              map args
          | [Basic (.ExprWithAttr _) .., a] =>
            "\\cdots" :: map [a]
          | args@([Basic (.UnaryPrefix op) .., a]) =>
            if op.func.priority == 76 then
              "\\cdots" :: map [a]
            else
              map args
          | args =>
            map args
        | .Lean_operatorname `id =>
          if let some rows := e.blockMatrixRows then
            map rows.flatten
          else
            map args
        | .Lean_operatorname `Tensor.eye =>
          []
        | _ =>
          map args
    | .UnaryPrefix ⟨`Not⟩ =>
      match args with
      | [arg] =>
        if arg.is_Mem then
          latexArgs arg
        else if let some x := arg.tendsToLatexArg? then
          [x.toLatex]
        else
          map args
      | _ =>
        map args
    | _ =>
      map args

  | Binder _ _ binderType value =>
    if value == nil then
      [binderType.toLatex]
    else
      [binderType.toLatex, value.toLatex]

  map : List Expr → List String
  | [] => []
  | head :: tail => ("{%s}".format head.toLatex) :: map tail

  flattenedDiv : Expr → String
  | e@(Basic (.BinaryInfix ⟨op⟩) [left, right] _) =>
    match op with
    | `Div.div
    | `HDiv.hDiv
    | `Rat.divInt =>
      "\\left. {%s} \\right/ {%s}".format left.toLatex, (if right.is_Div then flattenedDiv right else right.toLatex)
    | _ =>
      e.toLatex
  | e =>
    e.toLatex

  merge_ite : Expr → List String → List String
  | Basic (.Special ⟨`ite⟩) args _, cases =>
    match args with
    | [ifBranch, thenBranch, elseBranch] =>
      let ifBranch :=
        match ifBranch with
        | Binder .given name type nil =>
          "{%s} : {%s}".format name.toString.bvarLatex.escape_specials, type.toLatex
        | _ =>
          ifBranch.toLatex
      let cases := cases.concat ("{{%s}} & {\\color{blue}\\text{if}}\\ %s ".format thenBranch.toLatex, ifBranch)
      merge_ite elseBranch cases
    | _=>
      cases
  | e, cases =>
    cases.concat e.toLatex

def Expr.latex_tagged (expr : Expr) (hypId : Name) (color : String := "green") : String :=
  "%s\\tag*{$\\color{%s}%s$}".format expr.toLatex, color, (hypId.escape_specials ".")
