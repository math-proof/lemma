import Def.Lean.Level
import Def.Lean.Name
import Def.Data.List.List.Basic
import Def.Lean.Expr.Part11
import Inductive.Lean.PrettyPrinter.Latex
open Lean (Name)
set_option linter.unusedVariables false


partial def Expr.peelExpectLets : Expr → Expr × List Name
  | e@(Basic (.ExprWithLimits .Lean_let) args _) =>
    match args with
    | body :: binders =>
      let names := binders.filterMap fun b =>
        match b with
        | Binder _ name _ _ => some name
        | _ => none
      let (body', more) := body.peelExpectLets
      (body', names ++ more)
    | _ => (e, [])
  | e => (e, [])

def Expr.peelExpectObservable? : Expr → Option (Expr × List Name)
  | Basic (.ExprWithLimits .Lean_lambda) (body :: _) _ =>
    some body.peelExpectLets
  | _ => none

def Expr.symbolName? : Expr → Option Name
  | Symbol name _ => some name
  | _ => none

partial def Expr.markNamesAsRandomVariable (e : Expr) (names : List Name) : Expr :=
  if names.isEmpty then e
  else match e with
  | Symbol name type =>
    if names.contains name then markAsRandomVariable (Symbol name type)
    else Symbol name type
  | Basic func args level =>
    Basic func (args.map (·.markNamesAsRandomVariable names)) level
  | Binder b n t v =>
    Binder b n (t.markNamesAsRandomVariable names) (v.markNamesAsRandomVariable names)
  | other => other

/-- Like `markNamesAsRandomVariable`, marking the named symbols as random arguments (magenta). -/
partial def Expr.markNamesAsRandomArgument (e : Expr) (names : List Name) : Expr :=
  if names.isEmpty then e
  else match e with
  | Symbol name type =>
    if names.contains name then markAsRandomArgument (Symbol name type)
    else Symbol name type
  | Basic func args level =>
    Basic func (args.map (·.markNamesAsRandomArgument names)) level
  | Binder b n t v =>
    Binder b n (t.markNamesAsRandomArgument names) (v.markNamesAsRandomArgument names)
  | other => other

/-- `free`: names bound in the observable that are free random arguments (the `y` of
`𝔼[x: π | y](…)`, lean.js `expectBinderNames.free`); they render magenta instead of red. -/
def Expr.expectationFromObservable (μ x f : Expr) (mkApp : Expr → Expr → ExpectationView)
    (mkBody : Expr → Expr → Expr → ExpectationView) (free : List Name := []) : ExpectationView :=
  let rv := markAsRandomVariable x.stripAsRV
  match f.peelExpectObservable? with
  | some (body, letNames) =>
    let names := rv.symbolName?.toList ++ letNames.filter (!free.contains ·)
    let body := (body.markNamesAsRandomVariable names).markNamesAsRandomArgument
      (letNames.filter free.contains)
    mkBody body rv μ
  | none => mkApp f rv

def Expr.asExpectation? : Expr → Option ExpectationView
  | e =>
    match e.asNamedApp? with
    | some ("ofRV", μ :: x :: f :: _) =>
      some (expectationFromObservable μ x f
        (fun f rv => .map f rv)
        (fun body rv μ => .mapBody body rv μ))
    | some ("condRV", μ :: x :: y :: f :: _) =>
      some (expectationFromObservable μ x f
        (fun f rv => .cond f rv (markAsRandomVariable y))
        (fun body rv μ => .condBody body rv (markAsRandomVariable y) μ))
    | some ("condEvent", μ :: x :: y :: f :: _) =>
      some (expectationFromObservable μ x f
        (fun f rv => .cond f rv (markAsRandomVariable y))
        (fun body rv μ => .condBody body rv (markAsRandomVariable y) μ))
    | some ("condSigma", μ :: x :: y :: f :: _) =>
      let ys := [markAsRandomArgument y]
      some (expectationFromObservable μ x f
        (fun f rv => .condSigma f rv ys)
        (fun body rv μ => .condSigmaBody body rv ys μ))
    -- `𝔼[x: π | y](body)`: the free `y` is a random argument (magenta, also in the body)
    | some ("partialRV", μ :: x :: y :: f :: _) =>
      let ys := [markAsRandomArgument y.stripAsRV]
      some (expectationFromObservable μ x f
        (fun f rv => .condSigma f rv ys)
        (fun body rv μ => .condSigmaBody body rv ys μ) y.jointSymbolNames)
    -- `𝔼[x: π | y](body | r = r0)`: like lean.js, the observed `r` is a red random variable (`r0` dropped)
    | some ("partialRV_cond", μ :: x :: y :: r :: f :: _) =>
      let ys := [markAsRandomArgument y.stripAsRV, markAsRandomVariable r.stripAsRV]
      some (expectationFromObservable μ x f
        (fun f rv => .condSigma f rv ys)
        (fun body rv μ => .condSigmaBody body rv ys μ) y.jointSymbolNames)
    -- `partialRV_RA π x y r f`: `y` free, `r` conditioning random argument(s), both magenta
    | some ("partialRV_RA", μ :: x :: y :: r :: f :: _) =>
      let ys := [markAsRandomArgument y.stripAsRV, markAsRandomArgument r.stripAsRV]
      some (expectationFromObservable μ x f
        (fun f rv => .condSigma f rv ys)
        (fun body rv μ => .condSigmaBody body rv ys μ) y.jointSymbolNames)
    | _ => none

def Expr.asCondProbApp? : Expr → Option (String × List Expr)
  | Basic (.Special ⟨.anonymous⟩) [inner, pt] _ =>
    if let some ("condProb", base :: rest) := inner.asNamedApp? then
      some ("condProb", base :: rest ++ [pt])
    else none
  | _ => none

def Expr.asCondProb? : Expr → Option (Expr × Expr × Expr)
  | e =>
    let e := e.peelToReal
    let fromJoint (base pair : Expr) : Option (Expr × Expr × Expr) :=
      match pair.asJointRandomSymbol? with
      | some (x, y) => some (base, markAsRandomVariable x, markAsRandomVariable y)
      | none => none
    if let some ("condProb", base :: rest) := e.asNamedApp? then
      match rest with
      | [pair] => fromJoint base pair
      | [pair, point] =>
        if point.isCondProbPoint then fromJoint base pair else none
      | _ => none
    else if let some ("probCond", base :: xy :: _) := e.asNamedApp? then
      fromJoint base xy
    else if let some ("probCondRA", base :: xy :: _) := e.asNamedApp? then
      fromJoint base xy
    else if let some ("condProbRA", base :: xy :: _) := e.asNamedApp? then
      fromJoint base xy
    else if let some ("condProb", base :: rest) := e.asCondProbApp? then
      match rest with
      | [pair, point] =>
        if point.isCondProbPoint then fromJoint base pair else none
      | _ => none
    else none

/-- In `body`, find `condProb μ (x, y) (binder, _)` or `(_, binder)` (after `toReal`) and return the
RV whose value is the `∑ «·.bvar» t` sum binder — lean.js index `a t` / `s (t + 1)`.
Handles both the flat method app and the curried `(μ.condProb pair) point` form. -/
partial def Expr.condProbSumRV? (e : Expr) (binder : Name) : Option Expr :=
  let e := e.peelToReal
  let fromPoint (pair point : Expr) : Option Expr :=
    match pair.asJointRandomSymbol?, point with
    | some (x, y), Basic (.Special ⟨.str _ "mk"⟩) [a, b] _ =>
      -- sumAt residual: `(c, «s.bvar» t)` or `(«a.bvar» t, c)` — Symbol ↔ bound observation
      if a.symbolName?.isSome && b.isBoundObservation then some x
      else if b.symbolName?.isSome && a.isBoundObservation then some y
      else
        let eqBinder (e : Expr) : Bool :=
          match e.symbolName? with
          | some n => n.eraseMacroScopes == binder.eraseMacroScopes
          | none => false
        if eqBinder a then some x else if eqBinder b then some y else none
    | _, _ => none
  let fromArgs : List Expr → Option Expr
    | _base :: pair :: point :: _ => fromPoint pair point
    | _ => none
  match e.asCondProbApp? with
  | some ("condProb", args) => fromArgs args
  | _ =>
    match e.asNamedApp? with
    | some ("condProb", args) => fromArgs args
    | _ =>
      match e with
      | Basic _ args _ => args.findSome? (·.condProbSumRV? binder)
      | Binder _ _ t v => (t.condProbSumRV? binder).orElse fun _ => v.condProbSumRV? binder
      | _ => none

/-- `∑ c ∈ Finset.univ, body` arising from `∑ «a.bvar»[t], …` / `∑ «a.bvar» t, …` (see `sumAt` in
`Macro/Algebra/BigOperators/Summations.lean`) → `(a t, body[c ↦ a t])`, so the index prints as the RV
(lean.js) rather than `c ∈ Finset.univ`. Triggered by finding `condProb … (c, …)` in the body
(the sumAt residual), not by matching `Finset.univ` alone — that node's attr shape varies. -/
def Expr.asUnivCondProbSum? : Expr → Option (Expr × Expr)
  | Basic (.ExprWithLimits .Lean_sum) [body, Binder .contains name _set nil] _ =>
    match body.condProbSumRV? name with
    | some rv =>
      let rv := rv.markAsRandomVariable
      some (rv, body.replaceSymbol name rv)
    | none => none
  | _ => none

/-- Check if an Expr is of form `ae μ`. -/
def Expr.isAeMeasure (e : Expr) : Bool :=
  match e.asNamedApp? with
  | some ("ae", _) => true
  | _ => false

def Expr.asEventuallyEq? : Expr → Option (Expr × Expr)
  | e =>
    if let some ("EventuallyEq", [μ, f, g]) := e.asNamedApp? then
      if μ.isAeMeasure then some (f, g) else none
    else none

/-- `HasLaw X μ π` (Mathlib `ProbabilityTheory.HasLaw`) → `(X, μ, π)`.
    Latex matches lean.js `LeanDistributed`: `X \sim μ` (measure bracket elided). -/
def Expr.asHasLaw? : Expr → Option (Expr × Expr × Expr)
  | e =>
    if let some ("HasLaw", [x, μ, π]) := e.asNamedApp? then
      some (x, μ, π)
    else none

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
    level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
  let args := "\\ ".intercalate args
  if args.isEmpty then
    s!"{obj}.{attr}"
  else
    s!"{obj}.{attr}\\ {args}"

def BinaryInfix.latexFormat (op : BinaryInfix) (left right : Expr) (level : ℕ)
    (command : Option String := none) : String :=
  let func := op.func
  let opStr := command.getD func.command
  -- (`toColor ignore`: `true` drops the parentheses) a tuple keeps its parentheses; so does a lambda on the
  -- left, whose body would otherwise swallow the operator (`(fun x ↦ x t) = …`)
  let left := level.toColor ((left.priority ≥ func.priority || left.is_EnclosedGroup) && !left.is_JointRandomSymbol && !left.is_Lambda)
  let right := level.toColor ((right.priority > func.priority || right.is_Div || right.is_BlockMatrix) && !right.is_JointRandomSymbol)
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
          -- Subscript atoms (`a_i` / GetElem / toFun / juxta-index) need no pow parens.
          let base := left.peelLatexCoe
          let left := level.toColor (
            base.priority ≥ func.priority || base.is_EnclosedGroup || base.is_SubscriptAtom)
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
      if op.getLast == `toFun then
        let (base, indices) := e.collectToFunChain
        if !indices.isEmpty then
          let baseFmt := level.toColor (base.priority > func.priority || base.is_EnclosedGroup || base.is_LeanProperty || base.is_Eye)
          baseFmt ++ "_{" ++ ", ".intercalate (["%s"].repeat indices.length) ++ "}"
        else if let [arg] := args then
          let arg := level.toColor (arg.priority ≥ func.priority || arg.is_EnclosedGroup)
          let arg := if func.priority == 76 then "\\ " ++ arg else arg
          s!"{opStr}{arg}"
        else
          op.toString
      else if let [arg] := args then
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
          | `Complex.conj
          | `Star.star =>
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
        | .Lean_sum =>
          -- Nested plain ∑∑ → one ∑ with stacked limits (lean.js nestedSumChain).
          if e.nestedSumChain?.isSome then
            opStr ++ "\\limits_{\\substack{%s}} {%s}"
          else if e.asIcoClosed?.isSome then
            opStr ++ "\\limits_{%s=%s}^{%s} {%s}"
          else if e.asRangeClosedBound?.isSome then
            opStr ++ "\\limits_{%s=0}^{%s} {%s}"
          else if e.asRangeBound?.isSome || e.asIioBound?.isSome || e.asFinSumBound?.isSome then
            opStr ++ "\\limits_{%s < %s} {%s}"
          else if e.asIicBound?.isSome then
            opStr ++ "\\limits_{%s \\le %s} {%s}"
          else if e.asUnivCondProbSum?.isSome then
            opStr ++ "\\limits_{\\substack{%s}} {%s}"
          else
            opStr ++ "\\limits_{\\substack{%s}} {%s}"
        | .Lean_prod
        | .Lean_bigcup
        | .Lean_bigcap =>
          if e.asIcoClosed?.isSome then
            opStr ++ "\\limits_{%s=%s}^{%s} {%s}"
          else if e.asRangeClosedBound?.isSome then
            opStr ++ "\\limits_{%s=0}^{%s} {%s}"
          else if e.asRangeBound?.isSome || e.asIioBound?.isSome || e.asFinSumBound?.isSome then
            opStr ++ "\\limits_{%s < %s} {%s}"
          else if e.asIicBound?.isSome then
            opStr ++ "\\limits_{%s \\le %s} {%s}"
          else
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
        if let some (_, subs) := e.asSubst? then
          Expr.substLatexFormat subs.length
        else if let some (obj, fns) := e.asMap? then
          let obj := level.toColor (obj.priority > func.priority || obj.toList != none || obj.is_Eye)
          let fns := fns.map fun arg =>
            (0 : Nat).toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
          "\\ ".intercalate (obj :: fns)
        else if e.is_JuxtaIndexApp then
          -- `a i` / `a i j` → `{a}_{i}` / `{a}_{i, j}` (match GetElem / toFun)
          match args with
          | base :: indices =>
            let baseFmt := level.toColor (
              base.priority > func.priority || base.is_EnclosedGroup || base.is_LeanProperty ||
                base.is_Eye || base.is_SubscriptAtom)
            baseFmt ++ "_{" ++ ", ".intercalate (["%s"].repeat indices.length) ++ "}"
          | _ =>
            opStr
        else
          let args := args.zipIdx.map fun ⟨arg, i⟩ =>
            level.toColor (((i == 0 || arg.priority > func.priority) && (i > 0 || arg.priority ≥ func.priority) || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
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
      if e.unwrapAsRV?.isSome then
        "%s"
      else if let some ("toReal", _) := e.asNamedApp? then
        -- lean.js `toReal` → `%s` (ENNReal→ℝ); also lets inner `condProb` hit `asCondProb?`
        "%s"
      else if let some ("RandomVariable", [_]) := e.asNamedApp? then
        -- value-level wrap of a Lean_function head (`a` in `a t`) → red plain name
        "{\\color{red} {%s}}"
      else if let some (_, subs) := e.asSubst? then
        Expr.substLatexFormat subs.length
      else if let some (_, _, point) := e.asGradient? then
        match point with
        | none => "\\nabla_{%s} {%s}"
        | some _ => "\\left. \\nabla_{%s} {%s} \\right|_{{%s} = {%s}}"
      else if let some (_binderName, _fn, μ) := e.asIntegral? then
        if μ.isVolume then
          "\\int {%s}\\, {\\color{blue}\\mathrm{d}}{%s}"
        else
          "\\int {%s}\\, {\\color{blue}\\partial}{%s}"
      else if let some (_binderName, _fn, μ) := e.asLintegral? then
        if μ.isVolume then
          "\\int^{⁻} {%s}\\, {\\color{blue}\\mathrm{d}}{%s}"
        else
          "\\int^{⁻} {%s}\\, {\\color{blue}\\partial}{%s}"
      else if let some view := e.asExpectation? then
        match view with
        | .map _ _ =>
          "\\mathop{\\mathbb{E}}\\limits_{%s}\\left(%s\\ %s\\right)"
        | .mapBody _ _ _ =>
          "\\mathop{\\mathbb{E}}\\limits_{%s : %s}\\left(%s\\right)"
        | .cond _ _ _ =>
          "\\mathop{\\mathbb{E}}\\limits_{%s}\\left(%s\\ %s\\,\\mid\\,%s\\right)"
        | .condBody _ _ _ _ =>
          "\\mathop{\\mathbb{E}}\\limits_{%s : %s}\\left(%s\\,\\mid\\,%s\\right)"
        | .condSigma _ _ ys =>
          "\\mathop{\\mathbb{E}}\\limits_{%s}\\left(%s\\ %s\\,\\middle|\\," ++
            ", ".intercalate (ys.map fun _ => "%s") ++ "\\right)"
        | .condSigmaBody _ _ ys _ =>
          "\\mathop{\\mathbb{E}}\\limits_{%s : %s}\\left(%s\\,\\middle|\\," ++
            ", ".intercalate (ys.map fun _ => "%s") ++ "\\right)"
      else if let some (_, _) := e.asJointRandomSymbol? then
        "%s, %s"
      else if let some (_, _, _) := e.asEventuallyAe? then
        "\\forall^{ᵐ}\\,{%s}, {%s}"
      else if let some (_obj, fns) := e.asProb? then
        let slots := ", ".intercalate (List.replicate fns.length "%s")
        "{\\mathbb{P}}_{%s}\\left(" ++ slots ++ "\\right)"
      else if let some (obj, fns) := e.asMap? then
        let obj := level.toColor (obj.priority > func.priority || obj.toList != none || obj.is_Eye)
        let fns := fns.map fun arg =>
          (0 : Nat).toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
        "\\ ".intercalate (obj :: fns)
      else if let some (_obj, _, _) := e.asCondProb? then
        "{\\mathbb{P}}_{%s}\\left(%s\\,\\middle|\\,%s\\right)"
      else if let some (_, _) := e.asEventuallyEq? then
        "{%s} {=^{\\mathrm{m}}} {%s}"
      else if let some (_, _, _) := e.asHasLaw? then
        -- lean.js LeanDistributed: `{%s} \\sim {%s}` (π elided)
        "{%s} \\sim {%s}"
      else if let some (_) := e.asEtaPair? then
        "%s, %s"
      else match op with
      | .Lean_function _ =>
        let args := args.map fun arg =>
          level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
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
              level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
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
        | `Tensor.matProd
        | `Matrix.matProd =>
          match Expr.asMatProd? e with
          | some _ =>
            "\\prod\\limits_{%s < %s} {%s}"
          | none =>
            let args := args.map fun arg =>
              level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
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
              level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
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
        | `chiSquare
        | `Real.chiSquare =>
          -- js/php: Real.chiSquare / chiSquare n -> \\mathcal{X}^{2}\\left(n\\right) (bare -> \\mathcal{X}^{2})
          match args with
          | [_] => "\\mathcal{X}^{2}\\left(%s\\right)"
          | [] => "\\mathcal{X}^{2}"
          | _ =>
            let args := args.map fun arg =>
              level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
            opStr ++ "\\ " ++ "\\ ".intercalate args
        | `ProbabilityTheory.gaussianReal =>
          -- js/php: gaussianReal mu sigma -> \\mathcal{N}\\left(mu, sigma\\right) (bare -> \\mathcal{N})
          match args with
          | [_, _] => "\\mathcal{N}\\left(%s, %s\\right)"
          | [] => "\\mathcal{N}"
          | _ =>
            let args := args.map fun arg =>
              level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
            opStr ++ "\\ " ++ "\\ ".intercalate args
        | `Function.getSliceFrom =>
          -- Python open slice `f[t:]` = `Function.getSliceFrom f t` → `{f}_{t:}` (lean.js `{f}_{t : }`)
          "{%s}_{%s:}"
        | `Function.getSlice =>
          -- `x[start:stop:step]` for a family `x : ℕ → β` (same shapes as the `LeanMethod` `getSlice` below)
          match args with
          | [_, Basic (.Special ⟨`Slice.mk⟩) [start, _, step] _] =>
            if let const (.natVal 1) := step then
              if let const (.natVal 0) := start then "{%s}_{:%s}" else "{%s}_{%s:%s}"
            else
              if let const (.natVal 0) := start then "{%s}_{:%s:%s}" else "{%s}_{%s:%s:%s}"
          | _ => opStr ++ "\\ " ++ "\\ ".intercalate (args.map fun arg => level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol))
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
          -- Mathlib: `f ⁻¹' s`; `f^{-1}[s]` like lean.js (a trailing `'` after `^{-1}` is a KaTeX double superscript)
          "{%s}^{-1}\\left[{%s}\\right]"
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
              level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
            opStr ++ "\\ " ++ "\\ ".intercalate args
          else
            postOp
        | _  =>
          let args := args.map fun arg =>
            level.toColor ((arg.priority > func.priority || arg.is_Div || arg.is_BlockMatrix) && !arg.is_JointRandomSymbol)
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
            "{%s}^{-1}\\left[{%s}\\right]"
          else
            opStr
        | "descFactorial", [_, _] =>
          "{%s}^{\\underline{%s}}"
        | "ascFactorial", [_, _] =>
          "{%s}^{\\overline{%s}}"
        | "traj", [M, θ] =>
          -- `Model.traj M θ` / `M.traj θ` / CoeFun `M θ` → `M θ` (lean.js + `traj.unexpand`)
          let M := level.toColor (M.priority > func.priority || M.toList != none || M.is_Eye)
          let θ := level.toColor (θ.priority > func.priority || θ.is_Div || θ.is_BlockMatrix)
          s!"{M}\\ {θ}"
        | "toFun", _ =>
          let (base, indices) := e.collectToFunChain
          if indices.isEmpty then
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
          else
            let baseFmt := level.toColor (base.priority > func.priority || base.is_EnclosedGroup || base.is_LeanProperty || base.is_Eye)
            baseFmt ++ "_{" ++ ", ".intercalate (["%s"].repeat indices.length) ++ "}"
        | "getSliceFrom", [_, _] =>
          "{%s}_{%s:}"
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
        if name.getLast == `toFun then
          let (base, indices) := e.collectToFunChain
          if !indices.isEmpty then
            let baseFmt := level.toColor (base.priority > func.priority || base.is_EnclosedGroup || base.is_LeanProperty || base.is_Eye)
            baseFmt ++ "_{" ++ ", ".intercalate (["%s"].repeat indices.length) ++ "}"
          else
            match args with
            | arg :: _ =>
              let arg := level.toColor (arg.priority ≥ func.priority || arg.toList != none || arg.is_Eye)
              s!"{arg}.{attr}"
            | .nil =>
              name.toString.escape_specials
        else
          match name with
          | `Complex.exp =>
            "{\\color{RoyalBlue} e} ^ %s"
          | `Complex.cos
          | `Complex.sin
          | `Complex.log =>
            s!"\\{attr} %s"
          | `IsConstant.is_constant =>
            "%s\\ {\\color{blue}\\text{is}}\\ {constant}"
          | `Tensor.T
          | `Matrix.transpose =>
            "{%s}^{\\color{magenta} T}"
          | `Matrix.conjTranspose =>
            "{%s}^{\\color{magenta} {\\dagger}}"
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
  -- lean.js `markRandomVarNames`: once Prob/joint RVs reveal head names (`a`, `s`), recolor every
  -- matching head in the goal (including `V θ t (s t)` / `«s.bvar» t`), skipping magenta RAs.
  let e := e.markNamesAsRVHeads (e.foldRVHeadNames [])
  e.latexFormat.printf (latexArgs e)
where
  /-- Limit fragment for one ∑ in a nested chain (no body). Mirrors lean.js `sumLimitLatex`. -/
  sumLimitLatex : Expr → String
  | e =>
    if let some (i, a, b, _) := e.asIcoClosed? then
      "{%s} \\le {%s} \\le {%s}".format a.toLatex, i, b.toLatex
    else if let some (i, top, _) := e.asRangeClosedBound? then
      "0 \\le {%s} \\le {%s}".format i, top.toLatex
    else if let some (i, n, _) := e.asRangeBound? <|> e.asIioBound? <|> e.asFinSumBound? then
      "{%s} < {%s}".format i, n.toLatex
    else if let some (i, k, _) := e.asIicBound? then
      "{%s} \\le {%s}".format i, k.toLatex
    else if let some (rv, _) := e.asUnivCondProbSum? then
      rv.toLatex
    else
      match e with
      | Basic (.ExprWithLimits .Lean_sum) [_, binder@(Binder .contains ..)] _ =>
        binder.toLatex
      | Basic (.ExprWithLimits .Lean_sum) [_, Binder .default name type nil] _ =>
        "{%s : %s}".format name.toString.bvarLatex.escape_specials, type.toLatex
      | _ =>
        ""
  latexArgs : Expr → List String
  | nil => []

  | const val =>
    [val.toLatex]

  | sort u =>
    [u.toString]

  | Symbol name type =>
    if type.isRandomArgument then
      ["{\\color{magenta} {" ++ name.bvarLatex "." ++ "}}"]
    else if type.isRandomVariable then
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
        | .Lean_sum =>
          match e.nestedSumChain? with
          | some (chain, body) =>
            -- Inner binder first (evaluation / sympy substack order), then outer.
            let limits := " \\\\ ".intercalate (chain.reverse.map sumLimitLatex)
            [limits, body.toLatex]
          | none =>
            match e.asIcoClosed? with
            | some (i, a, b, body) =>
              [i, a.toLatex, b.toLatex, body.toLatex]
            | none =>
              match e.asRangeClosedBound? with
              | some (i, top, body) =>
                [i, top.toLatex, body.toLatex]
              | none =>
                match e.asRangeBound? <|> e.asIioBound? <|> e.asFinSumBound? with
                | some (i, n, body) =>
                  [i, n.toLatex, body.toLatex]
                | none =>
                  match e.asIicBound? with
                  | some (i, k, body) =>
                    [i, k.toLatex, body.toLatex]
                  | none =>
                    match e.asUnivCondProbSum? with
                    | some (rv, body) =>
                      -- lean.js: index is the RV `a t` / `s (t+1)` (not red — it is the bound value)
                      [rv.toLatex, body.toLatex]
                    | none =>
                      match args with
                      | [expr, Binder .default name type nil] =>
                        [("{%s : %s}".format name.toString.bvarLatex.escape_specials, type.toLatex), expr.toLatex]
                      | _ =>
                        []
        | .Lean_prod
        | .Lean_bigcup
        | .Lean_bigcap =>
          match e.asIcoClosed? with
          | some (i, a, b, body) =>
            [i, a.toLatex, b.toLatex, body.toLatex]
          | none =>
            match e.asRangeClosedBound? with
            | some (i, top, body) =>
              [i, top.toLatex, body.toLatex]
            | none =>
              match e.asRangeBound? <|> e.asIioBound? <|> e.asFinSumBound? with
              | some (i, n, body) =>
                [i, n.toLatex, body.toLatex]
              | none =>
                match e.asIicBound? with
                | some (i, k, body) =>
                  [i, k.toLatex, body.toLatex]
                | none =>
                  match args with
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
        if let some (body, subs) := e.asSubst? then
          Expr.substLatexArgs body subs (·.toLatex)
        else if let some (obj, fns) := e.asMap? then
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
      if let some x := e.unwrapAsRV? then
        [x.toLatex]
      else if let some ("toReal", [x]) := e.asNamedApp? then
        [x.toLatex]
      else if let some ("RandomVariable", [inner]) := e.asNamedApp? then
        [inner.rvDisplayName]
      else if let some (body, subs) := e.asSubst? then
        Expr.substLatexArgs body subs (·.toLatex)
      else if let some (x, body, point) := e.asGradient? then
        match point with
        | none => [x, body.toLatex]
        | some p => [x, body.toLatex, x, p.toLatex]
      else if let some (binderName, fn, μ) := e.asIntegral? then
        if μ.isVolume then [fn.toLatex, binderName] else [fn.toLatex, μ.toLatex]
      else if let some (binderName, fn, μ) := e.asLintegral? then
        if μ.isVolume then [fn.toLatex, binderName] else [fn.toLatex, μ.toLatex]
      else if let some view := e.asExpectation? then
        match view with
        | .map f rv => [rv.toLatex, f.toLatex, rv.toLatex]
        | .mapBody body rv μ => [rv.toLatex, μ.toLatex, body.toLatex]
        | .cond f x y => [x.toLatex, f.toLatex, x.toLatex, y.toLatex]
        | .condBody body x y μ => [x.toLatex, μ.toLatex, body.toLatex, y.toLatex]
        | .condSigma f x ys => [x.toLatex, f.toLatex, x.toLatex] ++ ys.map (·.toLatex)
        | .condSigmaBody body x ys μ => [x.toLatex, μ.toLatex, body.toLatex] ++ ys.map (·.toLatex)
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
      else if let some (x, μ, _) := e.asHasLaw? then
        [x.toLatex, μ.toLatex]
      else if let some etaArgs := e.asEtaPair? then
        etaArgs.map (·.toLatex)
      else
        match op with
        | .LeanMethod op idx =>
          match op with
          | .str _ "toFun" =>
            let (base, indices) := e.collectToFunChain
            if indices.isEmpty then
              map (args.swap 0 idx)
            else
              map (base :: indices)
          | .str _ "getSliceFrom" =>
            map args  -- `f[t:]` → format `{%s}_{%s:}`, args [f, t]
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
            | [s, f] => preimageBase f :: map [s]
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
        | .Lean_operatorname `Tensor.matProd
        | .Lean_operatorname `Matrix.matProd =>
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
        | .Lean_operatorname `Set.preimage =>
          match args with
          | [f, s] => preimageBase f :: map [s]
          | _ => map args
        | .Lean_operatorname `Function.getSliceFrom =>
          -- `Function.getSliceFrom f t` → args [f, t] for `{%s}_{%s:}`
          map args
        | .Lean_operatorname `Function.getSlice =>
          if let [base, Basic (.Special ⟨`Slice.mk⟩) [start, stop, step] _] := args.map (fun a =>
              match a with
              | Basic f@(.Special ⟨`Slice.mk⟩) bounds level => Basic f (bounds.map stripNatCast) level
              | a => a) then
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
        | .Lean_operatorname `Tensor.eye =>
          []
        | .LeanProperty name =>
          if name.getLast == `toFun then
            let (base, indices) := e.collectToFunChain
            if indices.isEmpty then map args
            else map (base :: indices)
          else
            map args
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
    | .UnaryPrefix ⟨op⟩ =>
      if op.getLast == `toFun then
        let (base, indices) := e.collectToFunChain
        if indices.isEmpty then map args
        else map (base :: indices)
      else
        map args
    | _ =>
      map args

  | Binder _ _ binderType value =>
    if value == nil then
      [binderType.toLatex]
    else
      [binderType.toLatex, value.toLatex]

  /-- Base of `f^{-1}[s]`: like lean.js `LeanPreimage`, an applied function or a tuple is bracketed
  (`(s t)^{-1}[…]`), or it reads as `s (t^{-1})`. -/
  preimageBase (f : Expr) : String :=
    let paren : Bool :=
      match f with
      | Basic (.Special ⟨.anonymous⟩) .. => true
      | Basic (.Special ⟨.str _ "mk"⟩) .. => true
      | _ => (f.asNamedApp?.map (·.1)) == some "JointRandomSymbol"
    if paren then "{\\left(" ++ f.toLatex ++ "\\right)}" else "{" ++ f.toLatex ++ "}"

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

