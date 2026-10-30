import Def.Lean.Level
import Def.Lean.Name
import Def.Data.List.List.Basic
import Def.Lean.Expr.Part11
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

/-- True when `e` is a `*.toFun` structure projection / method head (`Fun.toFun`, …). -/
def Expr.isToFunHead : Expr → Bool
  | Basic (.ExprWithAttr (.LeanMethod name _)) _ _
  | Basic (.ExprWithAttr (.LeanProperty name)) _ _ =>
    name.getLast == `toFun
  | Basic (.UnaryPrefix ⟨name⟩) _ _ =>
    name.getLast == `toFun
  | _ => false

/-- Object + trailing index args of a `*.toFun` application, after method-idx swap.
`Fun.toFun x i` → `some (x, [i])`; bare `x.toFun` → `none`. -/
def Expr.asToFunApp? : Expr → Option (Expr × List Expr)
  | Basic (.ExprWithAttr (.LeanMethod _ idx)) args _ =>
    if args.length ≤ idx then none
    else
      match args.swap 0 idx with
      | obj :: index :: rest => some (obj, index :: rest)
      | _ => none
  | Basic (.ExprWithAttr (.LeanProperty _)) args _ =>
    match args with
    | obj :: index :: rest => some (obj, index :: rest)
    | _ => none
  | Basic (.UnaryPrefix _) args _ =>
    match args with
    | obj :: index :: rest => some (obj, index :: rest)
    | _ => none
  | _ => none

/--
Peel consecutive `*.toFun` applications into `(base, indices)`.
Used so `(x.toFun i).toFun j` becomes `{x}_{i, j}` (one subscript level), matching
`GetElem` / lean.js multi-index style (`x[i][j]` → `x_{i, j}`).
-/
partial def Expr.collectToFunChain : Expr → Expr × List Expr
  | e@(Basic (.ExprWithAttr (.LeanMethod name idx)) args _) =>
    if name.getLast != `toFun || args.length ≤ idx then
      (e, [])
    else
      match args.swap 0 idx with
      | obj :: index :: rest =>
        let (base, idxs) := obj.collectToFunChain
        (base, idxs ++ index :: rest)
      | _ =>
        (e, [])
  | e@(Basic (.ExprWithAttr (.LeanProperty name)) args _) =>
    if name.getLast != `toFun then
      (e, [])
    else
      match args with
      | obj :: index :: rest =>
        let (base, idxs) := obj.collectToFunChain
        (base, idxs ++ index :: rest)
      | _ =>
        (e, [])
  | e@(Basic (.UnaryPrefix ⟨name⟩) args _) =>
    if name.getLast != `toFun then
      (e, [])
    else
      match args with
      | obj :: index :: rest =>
        let (base, idxs) := obj.collectToFunChain
        (base, idxs ++ index :: rest)
      | _ =>
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

/-- `Tensor.matProd` / `Matrix.matProd n (fun i => body)` → `(i, n, body)`. -/
def Expr.asMatProd? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithAttr (.Lean_operatorname `Tensor.matProd)) [n, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default binderName _ nil] _] _
  | Basic (.ExprWithAttr (.Lean_operatorname `Matrix.matProd)) [n, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default binderName _ nil] _] _ =>
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

/-- See through `Prod.fst ⟨a, b⟩` / `Prod.snd ⟨a, b⟩` to the component `a` / `b`, also through nested
projections (`Prod.fst (Prod.snd (a, b, c))` ↦ `b`: the coercion `↑(a, b, c)` of `Function.coeProdPi3R`
unfolds to these). -/
partial def Expr.asPairProj? : Expr → Option Expr
  | e =>
    let isFst := e.isNamedApp "fst"
    if isFst || e.isNamedApp "snd" then
      match e with
      | Basic _ [inner] _ =>
        let inner := inner.asPairProj?.getD inner
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

/-- `JointRandomSymbol x y` renders bare as `x, y` (so `𝔼`/`ℙ` binders and conditioners read `x, y`); as an
operand (`=` side, function argument) it is the tuple `(x, y)` and must keep its parentheses. -/
def Expr.is_JointRandomSymbol (e : Expr) : Bool :=
  e.asJointRandomSymbol?.isSome

/-- `fun x ↦ body` (also an elaborated `·` section `(· t)`): as a left operand it needs parentheses,
since the lambda body would otherwise extend over the operator (`(fun x ↦ x t) = …`). -/
def Expr.is_Lambda : Expr → Bool
  | Basic (.ExprWithLimits .Lean_lambda) .. => true
  | _ => false

/-- An observed value: `«x.bvar»`, an indexed `«x.bvar» i`, a slice `«x.bvar»[a:b]`, or a
tuple / singleton / insert of those. Mirrors lean.js, which drops all of these from `ℙ[π](x = «x.bvar»)`. -/
partial def Expr.isBoundObservation : Expr → Bool
  | Symbol name _ =>
    let s := name.toString
    s.startsWith "«" && s.endsWith "»" && s.contains ".bvar"
  | Basic (.Special ⟨.str _ "mk"⟩) [a, b] _ =>
    a.isBoundObservation && b.isBoundObservation
  | Basic (.Special ⟨`Singleton.singleton⟩) [x] _
  | Basic (.Special ⟨`Insert.insert⟩) [x] _ =>
    x.isBoundObservation
  -- `«x.bvar» i` : application of a local variable (`get_args` builds `Special .anonymous (f :: args)`)
  | Basic (.Special ⟨.anonymous⟩) (f@(Symbol ..) :: _ :: _) _ =>
    f.isBoundObservation
  -- `«x.bvar»[a:b]` : `getSlice «x.bvar» (Slice.mk ..)`
  | e@(Basic _ _ _) =>
    match e.asNamedApp? with
    | some ("getSlice", b :: _)
    | some ("getSliceFrom", b :: _) => b.isBoundObservation
    | _ => false
  | _ => false

/-- `ENNReal.toReal` / `.toReal` (scoped `CoeTC ENNReal ℝ`); lean.js property `toReal` → `%s`. -/
partial def Expr.peelToReal : Expr → Expr
  | e =>
    match e.asNamedApp? with
    | some ("toReal", [x]) => x.peelToReal
    | _ => e

/-- Drop the evaluation point of `condProb` for the short form `ℙ(x | y)`, as lean.js drops
`= «x.bvar»`. Accepts a full bound observation or the residual after `∑ «a.bvar» t` elaborates to
`∑ c ∈ Finset.univ` (point `(c, «s.bvar» t)` / `(«a.bvar» t, c)` — only one side stays a `.bvar`). -/
def Expr.isCondProbPoint : Expr → Bool
  | e =>
    e.isBoundObservation ||
    match e with
    | Basic (.Special ⟨.str _ "mk"⟩) [a, b] _ =>
      a.isBoundObservation || b.isBoundObservation
    | _ => false

/-- Replace every `Symbol name` with `replacement` (display-only substitution for sum binders). -/
partial def Expr.replaceSymbol (e : Expr) (name : Name) (replacement : Expr) : Expr :=
  match e with
  | Symbol n _ => if n == name then replacement else e
  | Basic f args level => Basic f (args.map (·.replaceSymbol name replacement)) level
  | Binder b n t v =>
    Binder b n (t.replaceSymbol name replacement) (v.replaceSymbol name replacement)
  | other => other

/-- Wrap a `Symbol`'s type in `RandomVariable` so `isRandomVariable` returns true
and it renders red. Mirrors the JS `Measure.map` special case in
`markRandomVarNames` which marks the map argument as a random variable
regardless of whether `IsProbabilityMeasure` is present.

Like lean.js `markProbBinderArgs.markRV`, it also reaches the random-variable symbol inside an
applied family `x i` (`Special .anonymous (x :: _)`), a slice `x[a:b]` (`getSlice x _`) and a
tuple `(a, b)` of those. -/
partial def Expr.markAsRandomVariable : Expr → Expr
  | Symbol name type =>
    if type.isRandomVariable then Symbol name type
    else match type with
      -- keep magenta random-argument markers (condSigma conditioners)
      | Basic (.ExprWithAttr (.Lean_operatorname `RandomArgument)) [_] _ => Symbol name type
      | _ => Symbol name (.Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [type] type.level)
  -- Already wrapped (value-level RandomVariable around a function head)
  | e@(Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [_] _) => e
  | e@(Basic (.ExprWithAttr (.Lean_operatorname `RandomArgument)) [_] _) => e
  -- lean.js `headTokens`: mark the head of `a t` / `s (t+1)` (Symbol or Lean_function / operatorname)
  | Basic f@(.Special ⟨.anonymous⟩) (x :: rest) level =>
    Basic f (x.markAsRandomVariable :: rest) level
  | Basic f@(.Special ⟨.str _ "mk"⟩) [a, b] level =>
    Basic f [a.markAsRandomVariable, b.markAsRandomVariable] level
  | e@(Basic (.ExprWithAttr attr) args level) =>
    match attr with
    | .Lean_function _ | .Lean_operatorname _ | .LeanProperty _ | .LeanMethod _ _ =>
      if args.isEmpty then
        -- bare projection / const head `a` → wrap so latex prints `{\color{red} {a}}`
        -- Nonempty apps (`asRV x`, `JointRandomSymbol`, `a t`) stay intact here;
        -- `markNamesAsRVHeads` splits known RV heads (`a t`) without breaking asRV/joint.
        Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [e] level
      else e
    | _ => e
  | e@(Basic f (x :: rest) level) =>
    match e.asNamedApp? with
    | some ("getSlice", _)
    | some ("getSliceFrom", _) => Basic f (x.markAsRandomVariable :: rest) level
    | some ("JointRandomSymbol", _) => Basic f ((x :: rest).map markAsRandomVariable) level
    | _ => e
  | e => e

/-- True when `e` is marked as a random-argument type via the `RandomArgument` wrapper
(see `Expr.markAsRandomArgument`); such a `Symbol` renders magenta. -/
def Expr.isRandomArgument : Expr → Bool
  | Basic (.ExprWithAttr (.Lean_operatorname `RandomArgument)) [_] _ => true
  | _ => false

/-- Like `markAsRandomVariable`, but marks a *random argument* (magenta, lean.js `isRandomArgument`):
the conditioners `y` of `𝔼[x: π](f x | y t, z (t + 1))`. Only the head symbol is marked (lean.js
`markConditionerTerm` / `Lean.headTokens`: in `s t` only `s` is magenta, the index `t` stays black);
it reaches the same shapes as `markAsRandomVariable`. -/
partial def Expr.markAsRandomArgument : Expr → Expr
  | Symbol name type =>
    if type.isRandomArgument then Symbol name type
    else
      let type := match type with
        | Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [t] _ => t
        | t => t
      Symbol name (.Basic (.ExprWithAttr (.Lean_operatorname `RandomArgument)) [type] type.level)
  | Basic f@(.Special ⟨.anonymous⟩) (x@(Symbol ..) :: rest) level =>
    Basic f (x.markAsRandomArgument :: rest) level
  | Basic f@(.Special ⟨.str _ "mk"⟩) [a, b] level =>
    Basic f [a.markAsRandomArgument, b.markAsRandomArgument] level
  | e@(Basic f (x :: rest) level) =>
    match e.asNamedApp? with
    | some ("getSlice", _)
    | some ("getSliceFrom", _) => Basic f (x.markAsRandomArgument :: rest) level
    | some ("JointRandomSymbol", _) => Basic f ((x :: rest).map markAsRandomArgument) level
    | _ => e
  | e => e

/-- lean.js token text for RV-head matching: last segment, `«x.bvar»` → `x`. -/
def rvToken (n : Name) : String :=
  let n := n.eraseMacroScopes
  -- Prefer full-name bvar strip (`«s.bvar»` is often a single Name segment including guillemets),
  -- then fall back to the last segment (for `Foo.a` / hygienic names).
  let full := n.toString.bvarLatex
  if full != n.toString then full
  else n.getLast.toString.bvarLatex

/-- Name key used in RV-head lists (always `mkSimple` of `rvToken`). -/
def rvKey (n : Name) : Name :=
  Name.mkSimple (rvToken n)

/-- Membership by lean.js token text (avoids `Name` equality pitfalls across attr vs Symbol). -/
def rvNamesContain (names : List Name) (n : Name) : Bool :=
  let t := rvToken n
  names.any (fun m => rvToken m == t)

/-- Head of `a`, `a t`, `a (t+1)`, `a[t:]` (lean.js `headTokens`). -/
partial def Expr.headName? : Expr → Option Name
  | Symbol name _ => some (rvKey name)
  | Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [inner] _
  | Basic (.ExprWithAttr (.Lean_operatorname `RandomArgument)) [inner] _ => inner.headName?
  | Basic (.Special ⟨.anonymous⟩) (f :: _) _ => f.headName?
  | e@(Basic (.ExprWithAttr attr) _ _) =>
    match e.asNamedApp? with
    | some ("asRV", [x]) => x.headName?
    | some ("getSlice", b :: _) | some ("getSliceFrom", b :: _) => b.headName?
    | _ =>
      match attr with
      | .Lean_function n | .Lean_operatorname n | .LeanProperty n
      | .LeanMethod n _ | .LeanLemma n | .Lean_typeclass n => some (rvKey n)
  | _ => none

/-- Display text for a red RV head: plain `a`, not `\\operatorname{a}` (lean.js token latex). -/
def Expr.rvDisplayName : Expr → String
  | Symbol name _ => name.bvarLatex "."
  | Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [inner] _
  | Basic (.ExprWithAttr (.Lean_operatorname `RandomArgument)) [inner] _ => inner.rvDisplayName
  | Basic (.ExprWithAttr attr) _ _ =>
    attr.name.getLast.toString.escape_specials
  | e =>
    match e.headName? with
    | some n => n.toString.escape_specials
    | none => ""

/-- Collect RV head keys for a lean.js-style whole-tree recolor pass: Symbols already marked
random variables, and heads of `JointRandomSymbol` components (as in `condProb` / `prob`).
Does **not** collect `RandomArgument` names (magenta conditioners stay magenta). -/
partial def Expr.foldRVHeadNames (e : Expr) (acc : List Name) : List Name :=
  let add (n? : Option Name) (acc : List Name) : List Name :=
    match n? with
    | some n => if acc.contains n then acc else n :: acc
    | none => acc
  let acc :=
    match e with
    | Symbol _ type =>
      if type.isRandomVariable then add e.headName? acc else acc
    | Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [inner] _ =>
      add inner.headName? acc
    | _ =>
      match e.asJointRandomSymbol? with
      | some (x, y) =>
        -- a nested chain component `JointRandomSymbol y z` is no head: its own components are collected
        -- when the fold reaches it (otherwise `JointRandomSymbol` itself would be recolored and split into
        -- a plain application `JointRandomSymbol (s t) (…)` by `markNamesAsRVHeads`)
        let head (c : Expr) : Option Name := if c.is_JointRandomSymbol then none else c.headName?
        add (head y) (add (head x) acc)
      | none => acc
  match e with
  | Basic _ args _ => args.foldl (fun a x => x.foldRVHeadNames a) acc
  | Binder _ _ t v => v.foldRVHeadNames (t.foldRVHeadNames acc)
  | _ => acc

/-- Mark every head whose `rvKey` is in `names` (lean.js `markRandomVarNames`). Skips magenta
`RandomArgument` Symbols. -/
partial def Expr.markNamesAsRVHeads (e : Expr) (names : List Name) : Expr :=
  if names.isEmpty then e
  else match e with
  | Symbol name type =>
    if rvNamesContain names name then markAsRandomVariable (Symbol name type)
    else Symbol name type
  | Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [_] _ => e
  | Basic (.ExprWithAttr (.Lean_operatorname `RandomArgument)) [_] _ => e
  | Basic f@(.Special ⟨.anonymous⟩) (x :: rest) level =>
    Basic f (x.markNamesAsRVHeads names :: rest.map (·.markNamesAsRVHeads names)) level
  | Basic f@(.Special ⟨.str _ "mk"⟩) [a, b] level =>
    Basic f [a.markNamesAsRVHeads names, b.markNamesAsRVHeads names] level
  | e@(Basic (.ExprWithAttr attr) args level) =>
    match attr with
    | .Lean_function n | .Lean_operatorname n | .LeanProperty n | .LeanMethod n _ =>
      if rvNamesContain names n then
        -- `a` or `a t`: mark the bare head (lean.js colors the token, index stays black)
        let head := Basic (.ExprWithAttr attr) [] level
        let head := markAsRandomVariable head
        if args.isEmpty then head
        else Basic (.Special ⟨.anonymous⟩) (head :: args.map (·.markNamesAsRVHeads names)) level
      else
        Basic (.ExprWithAttr attr) (args.map (·.markNamesAsRVHeads names)) level
    | _ => Basic (.ExprWithAttr attr) (args.map (·.markNamesAsRVHeads names)) level
  | Basic func args level =>
    match e.asNamedApp? with
    | some ("getSlice", _)
    | some ("getSliceFrom", _) =>
      match args with
      | x :: rest => Basic func (x.markNamesAsRVHeads names :: rest.map (·.markNamesAsRVHeads names)) level
      | [] => e
    | some ("JointRandomSymbol", _) =>
      Basic func (args.map (·.markNamesAsRVHeads names)) level
    | _ => Basic func (args.map (·.markNamesAsRVHeads names)) level
  | Binder b n t v =>
    Binder b n (t.markNamesAsRVHeads names) (v.markNamesAsRVHeads names)
  | other => other

/-- `Expectation.asRV x` (the transparent `𝔼` binder coercion `AsPathRV.path`) → `x`, also inside a
`JointRandomSymbol` chain, so `𝔼[r: π](…)` over a process `r : ℕ → Ω → ℝ` shows the binder `r`. -/
partial def Expr.stripAsRV : Expr → Expr
  | e@(Basic f args level) =>
    match e.asNamedApp? with
    | some ("asRV", [x]) => x.stripAsRV
    | some ("JointRandomSymbol", _) => Basic f (args.map stripAsRV) level
    | _ => e
  | e => e

/-- A bare `Expectation.asRV x` (outside an `𝔼` binder, e.g. `Measurable (Expectation.asRV r[t + 1:])`)
→ the random variable `x` marked red; applied, `Expectation.asRV x ω` → the application `x ω`. -/
def Expr.unwrapAsRV? (e : Expr) : Option Expr :=
  match e with
  | Basic (.ExprWithAttr _) _ level =>
    match e.asNamedApp? with
    | some ("asRV", [x]) => some x.stripAsRV.markAsRandomVariable
    | some ("asRV", x :: rest) =>
      some (Basic (.Special ⟨.anonymous⟩) (x.stripAsRV.markAsRandomVariable :: rest) level)
    | _ => none
  | _ => none

/-- Names of the random variables in a (right-nested) `JointRandomSymbol` chain of binders
`y` / `Expectation.asRV y` / `JointRandomSymbol (Expectation.asRV y) (Expectation.asRV z)`. -/
partial def Expr.jointSymbolNames (e : Expr) : List Name :=
  match e.stripAsRV with
  | Symbol name _ => [name]
  | e' =>
    match e'.asNamedApp? with
    | some ("JointRandomSymbol", args) => args.flatMap jointSymbolNames
    | _ => []

/-- `∑/∏ i ∈ Finset.Ico a (b + 1), f` → `(i, a, b, f)`; rendered `\\prod_{i=a}^{b}` like lean.js
`icoClosedBound`. -/
def Expr.asIcoClosed? : Expr → Option (String × Expr × Expr × Expr)
  | Basic (.ExprWithLimits op) [body, Binder .contains name set nil] _ =>
    match op with
    | .Lean_sum | .Lean_prod =>
      match set.asNamedApp? with
      | some ("Ico", [a, Basic (.BinaryInfix ⟨`HAdd.hAdd⟩) [b, const (.natVal 1)] _]) =>
        some (name.toString.bvarLatex.escape_specials, a, b, body)
      | _ => none
    | _ => none
  | _ => none


/-- `∑/∏ i ∈ Finset.range (e + 1), f` → `(i, e, f)`; rendered `\\sum_{i=0}^{e}` like lean.js
`rangeClosedBound`. Prefer this over `asRangeBound?`. -/
def Expr.asRangeClosedBound? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithLimits op) [body, Binder .contains name set nil] _ =>
    match op with
    | .Lean_sum | .Lean_prod =>
      match set.asNamedApp? with
      | some ("range", [Basic (.BinaryInfix ⟨`HAdd.hAdd⟩) [e, const (.natVal 1)] _]) =>
        some (name.toString.bvarLatex.escape_specials, e, body)
      | _ => none
    | _ => none
  | _ => none

/-- `∑/∏ i ∈ Finset.range n, f` → `(i, n, f)`; rendered `\\sum_{i < n}` like lean.js `rangeBound`. -/
def Expr.asRangeBound? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithLimits op) [body, Binder .contains name set nil] _ =>
    match op with
    | .Lean_sum | .Lean_prod =>
      match set.asNamedApp? with
      | some ("range", [n]) =>
        some (name.toString.bvarLatex.escape_specials, n, body)
      | _ => none
    | _ => none
  | _ => none

/-- `∑/∏ i ∈ Finset.Iio k, f` → `(i, k, f)`; rendered `\\sum_{i < k}` like lean.js `iioBound`. -/
def Expr.asIioBound? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithLimits op) [body, Binder .contains name set nil] _ =>
    match op with
    | .Lean_sum | .Lean_prod =>
      match set.asNamedApp? with
      | some ("Iio", [k]) =>
        some (name.toString.bvarLatex.escape_specials, k, body)
      | _ => none
    | _ => none
  | _ => none

/-- `∑/∏ i ∈ Finset.Iic k, f` → `(i, k, f)`; rendered `\\sum_{i \\le k}` like lean.js `iicBound`. -/
def Expr.asIicBound? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithLimits op) [body, Binder .contains name set nil] _ =>
    match op with
    | .Lean_sum | .Lean_prod =>
      match set.asNamedApp? with
      | some ("Iic", [k]) =>
        some (name.toString.bvarLatex.escape_specials, k, body)
      | _ => none
    | _ => none
  | _ => none

/-- `∑/∏ i : Fin n, f` → `(i, n, f)`; rendered `\\sum_{i < n}` (same sugar as lean.js `finRangeBound`). -/
def Expr.asFinSumBound? : Expr → Option (String × Expr × Expr)
  | Basic (.ExprWithLimits op) [body, Binder .default name (Basic (.ExprWithAttr (.Lean_typeclass `Fin)) [n] _) nil] _ =>
    match op with
    | .Lean_sum | .Lean_prod =>
      some (name.toString.bvarLatex.escape_specials, n, body)
    | _ => none
  | _ => none

/-- Display-only: nested plain `∑ i, ∑ j, body` → `(chain, body)` with `chain.length ≥ 2`
(outer first). Mirrors lean.js `Lean_sum.nestedSumChain`. `∑'` is `Lean_tsum` here, so it never
joins the chain. Parentheses are already gone after Lean elaboration into this Expr AST. -/
def Expr.nestedSumChain? : Expr → Option (List Expr × Expr)
  | e@(Basic (.ExprWithLimits .Lean_sum) _ _) =>
    let rec go (cur : Expr) (acc : List Expr) : List Expr × Expr :=
      match cur with
      | Basic (.ExprWithLimits .Lean_sum) [body, _] _ =>
        match body with
        | next@(Basic (.ExprWithLimits .Lean_sum) _ _) =>
          go next (acc ++ [next])
        | _ =>
          (acc, body)
      | _ =>
        (acc, cur)
    let (chain, body) := go e [e]
    if chain.length ≥ 2 then some (chain, body) else none
  | _ => none

/-- Slice bounds are `ℤ`, so `x[:t + 1]` elaborates to `x.getSlice ⟨0, ↑t + 1, 1⟩`; lean.js shows the
source `t + 1`. Drop the `ℕ → ℤ` casts in such arithmetic. -/
partial def Expr.stripNatCast : Expr → Expr
  | Basic (.UnaryPrefix ⟨`Nat.cast⟩) [a] _ => a.stripNatCast
  | Basic f@(.BinaryInfix _) args level => Basic f (args.map stripNatCast) level
  | e => e

def Expr.asProbApp? : Expr → Option (String × List Expr)
  | Basic (.Special ⟨.anonymous⟩) [inner, pt] _ =>
    if let some ("prob", base :: rest) := inner.asNamedApp? then
      some ("prob", base :: rest ++ [pt])
    else none
  | _ => none

def Expr.asProb? : Expr → Option (Expr × List Expr)
  | e =>
    let e := e.peelToReal
    if let some ("probRA", base :: x :: _) := e.asNamedApp? then
      some (base, [x.markAsRandomVariable])
    else if let some ("prob", base :: rest) := e.asNamedApp? then
      match rest with
      | [] => none
      | [_] => some (base, rest.map markAsRandomVariable)
      | _ =>
        if rest.getLast!.isBoundObservation then
          some (base, (rest.take (rest.length - 1)).map markAsRandomVariable)
        else
          none
    else if let some ("prob", base :: rest) := e.asProbApp? then
      match rest with
      | [] => none
      | _ =>
        if rest.getLast!.isBoundObservation then
          some (base, (rest.take (rest.length - 1)).map markAsRandomVariable)
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

/-- Spine of a `Subst` application: `«Subst» f x₀` or the curried `(«Subst» f x₀) y₀ …`
(a `Special .anonymous` application) → `(f, [x₀, y₀, …])`. -/
def Expr.substSpine? : Expr → Option (Expr × List Expr)
  | Basic (.Special ⟨.anonymous⟩) (inner :: rest) _ =>
    match inner.substSpine? with
    | some (f, vs) => some (f, vs ++ rest)
    | none => none
  | e =>
    match e.asNamedApp? with
    | some ("Subst", f :: vs@(_ :: _)) => some (f, vs)
    | _ => none

/-- sympy `Subs(expr, (x, y), (x0, y0))`: `Subst (expr | x = x₀ ∧ y = y₀)`, i.e.
`«Subst» (fun x y ↦ expr) x₀ y₀` → `(expr, [(x, x₀), (y, y₀)])`; `none` unless every binder of the
lambda receives a value. -/
def Expr.asSubst? (e : Expr) : Option (Expr × List (String × Expr)) :=
  match e.substSpine? with
  | some (Basic (.ExprWithLimits .Lean_lambda) (body :: limits) _, vs) =>
    -- same-typed binders are merged into one `Binder` with the hierarchical name `x.y`
    let binders := limits.reverse.filterMap fun
      | Binder .default name _ nil => some (name.components.map (·.bvarLatex "\\ "))
      | _ => none
    let names := binders.flatten
    if binders.length == limits.length && names.length == vs.length then
      some (body, names.zip vs)
    else
      none
  | _ => none

/-- `\left. expr \right|_{x = x₀}` (one variable) or
`\left. expr \right|_{\substack{x = x₀ \\ y = y₀}}` (sympy `_print_Subs`). -/
def Expr.substLatexFormat (n : Nat) : String :=
  let subs := " \\\\ ".intercalate (List.replicate n "{%s} = {%s}")
  if n == 1 then
    "\\left. {%s} \\right|_{" ++ subs ++ "}"
  else
    "\\left. {%s} \\right|_{\\substack{" ++ subs ++ "}}"

/-- LaTeX slots of `Expr.substLatexFormat`: body, then `name, value` per substitution. -/
def Expr.substLatexArgs (body : Expr) (subs : List (String × Expr)) (toLatex : Expr → String) :
    List String :=
  toLatex body :: subs.flatMap fun (x, v) => [x, toLatex v]

/-- sympy `Gradient`: `gradient (fun θ ↦ expr) p` → `(θ, expr, point)`, where `point` is `none` when `p` is
the bound name itself (`∇[θ] expr`) and `some p` otherwise (`∇[θ = p] expr`). Under
`Subst (∇[θ] expr | θ = θ₀)` the point is the `Subst` variable `θ`, so the inner form is `∇[θ] expr`. -/
def Expr.asGradient? (e : Expr) : Option (String × Expr × Option Expr) :=
  match e.asNamedApp? with
  | some ("gradient", [Basic (.ExprWithLimits .Lean_lambda) [body, Binder .default name _ nil] _, p]) =>
    match p with
    | Symbol point _ =>
      if name == point then
        some (name.bvarLatex "\\ ", body, none)
      else
        some (name.bvarLatex "\\ ", body, some p)
    | _ => some (name.bvarLatex "\\ ", body, some p)
  | _ => none

