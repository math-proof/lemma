import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Def.Probability.SymbolicProbability.Part2
import Theorem.Function
import Syntax.Probability.JointRv.Part5
open MeasureTheory
open scoped ProbabilityTheory


open Lean


/-- Syntax kind of `a[t]` (GetElem). Not `Array.«term__[_:]»` (`a[t:]`).
Under `open ProbabilityTheory`, Lean wraps GetElem in a `choice` node whose
alternatives include `ProbabilityTheory.«term__[_]»` as well as `«term__[_]»`. -/
def Expectation.Macro.isGetElemKind (k : SyntaxNodeKind) : Bool :=
  k == `«term__[_]» || k == `ProbabilityTheory.«term__[_]»

/-- Pick the GetElem alternative out of a `choice` (prefer std `«term__[_]»`). -/
def Expectation.Macro.asGetElem (e : Syntax) : Option Syntax :=
  if Expectation.Macro.isGetElemKind e.getKind then
    some e
  else if e.getKind == `choice then
    let args := e.getArgs
    match args.find? (fun a => a.getKind == `«term__[_]») with
    | some g => some g
    | none => args.find? (fun a => Expectation.Macro.isGetElemKind a.getKind)
  else
    none

/-- Head binder of an RA term: `a`, `a t`, or `a[t]` ↦ `a`; otherwise none. -/
def Expectation.Macro.raHead (e : Syntax) : Option Name :=
  if e.isIdent then
    some e.getId
  else if e.isOfKind ``Lean.Parser.Term.app then
    let fn := e[0]
    if fn.isIdent then some fn.getId else none
  else if let some ge := Expectation.Macro.asGetElem e then
    let coll := ge[0]
    if coll.isIdent then some coll.getId else none
  else
    none

/-- `a[t]` → `a t` so observation RHS works after path unpack (no GetElem on bare `ℕ → α`). -/
def Expectation.Macro.getElemAsApp (e : Syntax) : MacroM Term := do
  match Expectation.Macro.asGetElem e with
  | some ge =>
      let coll : Term := ⟨ge[0]⟩
      let idx : Term := ⟨ge[2]⟩
      `($coll $idx)
  | none => pure ⟨e⟩

/-- Replace the head binder of e by its alias when present (`a` / `a t` / `a[t]`).
GetElem `a[t]` becomes app `a₀ t` (via `getElemAsApp`) so RA observation LHS
does not keep GetElem after path unpack (`ℕ → α` has no usable GetElem vs Mathlib `P[X]`). -/
def Expectation.Macro.applyAlias (aliases : List (Name × Ident)) (e : Syntax) : MacroM Term := do
  if e.isIdent then
    match aliases.find? (fun p => p.1 == e.getId) with
    | some (_, a) => pure a
    | none => pure ⟨e⟩
  else if e.isOfKind ``Lean.Parser.Term.app then
    let fn := e[0]
    if fn.isIdent then
      match aliases.find? (fun p => p.1 == fn.getId) with
      | some (_, a) => pure ⟨e.setArg 0 a⟩
      | none => pure ⟨e⟩
    else
      pure ⟨e⟩
  else if let some ge := Expectation.Macro.asGetElem e then
    let coll := ge[0]
    if coll.isIdent then
      match aliases.find? (fun p => p.1 == coll.getId) with
      | some (_, a) => Expectation.Macro.getElemAsApp (ge.setArg 0 a)
      | none => Expectation.Macro.getElemAsApp ge
    else
      Expectation.Macro.getElemAsApp ge
  else
    pure ⟨e⟩

def Expectation.Macro.isAliasable (aliases : List (Name × Ident)) (e : Syntax) : Bool :=
  match Expectation.Macro.raHead e with
  | some n => aliases.any (fun p => p.1 == n)
  | none => false

/-- If `stx` is nested `𝔼[xs : π](b | ys,*)` whose conditioner heads are all in `aliases`,
rewrite to the observation / `condEvent` form. Returns `none` when `stx` is not that
RA-`𝔼` shape. Non-aliasable RA conditioners return the original node unchanged (caller
still `mapChildren`s). Standalone (empty aliases) never reaches here. -/
def Expectation.Macro.rewriteNestedExpectRA
    (aliases : List (Name × Ident)) (stx : Syntax) : MacroM (Option Syntax) := do
  match stx with
  | `(𝔼[$xs:ident,* : $π]($b:term | $ys:term,*)) =>
      let ysA := ys.getElems
      if !ysA.all (fun e => Expectation.Macro.isAliasable aliases e) then
        -- Keep RA surface → `condSigma` after elab; descend via `mapChildren`.
        return some stx
      let y ← ysA.mapM (Expectation.Macro.applyAlias aliases)
      let y0 ← ysA.mapM Expectation.Macro.getElemAsApp
      match y.size with
      | 0 => Macro.throwError "𝔼[…](… | …) requires at least one conditioning term"
      | 1 =>
          return some (← `(𝔼[$xs,* : $π]($b:term | $(y[0]!) = $(y0[0]!))))
      | _ =>
          let yHead := y[0]!
          let y0Head := y0[0]!
          let yRest := y.extract 1 y.size
          let y0Rest := y0.extract 1 y0.size
          return some (← `(𝔼[$xs,* : $π]($b:term | $yHead = $y0Head ∧ $[$yRest:term = $y0Rest:term]∧*)))
  | _ => return none

/-- Walk `stx` rewriting aliasable nested `ℙ` / `𝔼` RA sugar to observation form.
Called from every `𝔼` elaborator that builds outer aliases (including partial forms);
`mapChildren` descends into arbitrary operators (`𝕍𝕒𝕣`, `ℂ𝕠𝕧`, apps, …), so nested
`𝔼[…](b | ys,*)` is rewritten whenever *some* ancestor threaded `aliases`. -/
partial def Expectation.Macro.desugarProbRA (aliases : List (Name × Ident)) (stx : Syntax) :
    MacroM Syntax := do
  if aliases.isEmpty then
    return stx
  let rec go (s : Syntax) : MacroM Syntax := do
    if let some s' ← Expectation.Macro.rewriteNestedExpectRA aliases s then
      mapChildren s'
    else
      match s with
      | `(ℙ[$π]($xs:term,* | $ys:term,*)) =>
          let xsA := xs.getElems
          let ysA := ys.getElems
          if xsA.all (fun e => Expectation.Macro.isAliasable aliases e) &&
              ysA.all (fun e => Expectation.Macro.isAliasable aliases e) then
            let x ← xsA.mapM (Expectation.Macro.applyAlias aliases)
            let x0 ← xsA.mapM Expectation.Macro.getElemAsApp
            let y ← ysA.mapM (Expectation.Macro.applyAlias aliases)
            let y0 ← ysA.mapM Expectation.Macro.getElemAsApp
            `(ℙ[$π]($[$x:term = $x0:term]∧* | $[$y:term = $y0:term]∧*))
          else
            mapChildren s
      | `(ℙ[$π]($xs:term,* | $[$y:term = $y0:term]∧*)) =>
          let xsA := xs.getElems
          if xsA.all (fun e => Expectation.Macro.isAliasable aliases e) then
            let x ← xsA.mapM (Expectation.Macro.applyAlias aliases)
            let x0 ← xsA.mapM Expectation.Macro.getElemAsApp
            `(ℙ[$π]($[$x:term = $x0:term]∧* | $[$y:term = $y0:term]∧*))
          else
            mapChildren s
      | `(ℙ[$π]($xs:term,*)) =>
          let xsA := xs.getElems
          if xsA.all (fun e => Expectation.Macro.isAliasable aliases e) then
            let x ← xsA.mapM (Expectation.Macro.applyAlias aliases)
            let x0 ← xsA.mapM Expectation.Macro.getElemAsApp
            `(ℙ[$π]($[$x:term = $x0:term]∧*))
          else
            mapChildren s
      | _ => mapChildren s
  go stx
where
  mapChildren (s : Syntax) : MacroM Syntax := do
    let args ← s.getArgs.mapM (desugarProbRA aliases)
    return s.setArgs args

/-- `true` when `name` occurs in `stx` as an integrated *value* (anything that is not a
random-variable slot of a `ℙ`). Random-variable slots are RA terms (`ℙ[π](a t | s t)` —
the whole term is an RV slot) and the left-hand side of each `=`
(`ℙ[π](a t = u | s t = x)`). -/
partial def Expectation.Macro.bodyValueUse
    (stx : Syntax) (name : Name) (inRV : Bool := false) : MacroM Bool := do
  let rec goArgs (stxs : Array Syntax) (rv : Bool) : MacroM Bool :=
    stxs.foldlM (init := false) fun acc s => return acc || (← bodyValueUse s name rv)
  match stx with
  | `(ℙ[$_]($xs:term,*)) => goArgs xs (rv := true)
  | `(ℙ[$_]($xs:term,* | $ys:term,*)) =>
      return (← goArgs xs true) || (← goArgs ys true)
  | `(ℙ[$_]($xs:term,* | $[$y:term = $y0:term]∧*)) =>
      return (← goArgs xs true) || (← goArgs y true) || (← goArgs y0 false)
  | `(ℙ[$_]($[$x:term = $x0:term]∧* | $[$y:term = $y0:term]∧*)) =>
      return (← goArgs x true) || (← goArgs x0 false) || (← goArgs y true) || (← goArgs y0 false)
  | `(ℙ[$_]($[$x:term = $x0:term]∧* | $ys:term,*)) =>
      return (← goArgs x true) || (← goArgs x0 false) || (← goArgs ys true)
  | `(ℙ[$_]($[$x:term = $x0:term]∧*)) =>
      return (← goArgs x true) || (← goArgs x0 false)
  | _ =>
      if stx.isIdent then
        return !inRV && stx.getId == name
      else
        goArgs stx.getArgs inRV

open Lean.Elab.Term in
/-- Rebind a binder unless it is already a local whose body occurrences are all `ℙ` random-variable
slots (those must keep seeing the outer local). -/
def Expectation.Macro.rebindMask (xs : Array Syntax) (body : Syntax) : TermElabM (Array Bool) :=
  xs.mapM fun x => do
    let inScope := (← getLCtx).findFromUserName? x.getId |>.isSome
    if !inScope then
      return true
    else
      Lean.Elab.liftMacroM <| Expectation.Macro.bodyValueUse body x.getId

open Lean Meta Lean.Elab.Term in
/-- `true` when binder `x` is a local `Fun ℕ (· → ·)`, so the value path is re-wrapped with `Fun.mk`. -/
def Expectation.Macro.funBinderMask (xs : Array Syntax) : TermElabM (Array Bool) :=
  xs.mapM fun x => do
    let some ld := (← getLCtx).findFromUserName? x.getId | return false
    LiftRV.isFunProcess (← instantiateMVars (← inferType ld.toExpr))

open Lean.Elab.Term in
/-- Fresh `x₀`-style aliases for integrated binders that are already locals (outer processes). -/
def Expectation.Macro.mkOuterAliases (xs : Array Syntax) : TermElabM (List (Name × Ident)) := do
  let mut acc : List (Name × Ident) := []
  for x in xs do
    let n := x.getId
    if (← getLCtx).findFromUserName? n |>.isSome then
      let cand := Name.appendAfter n "₀"
      let aliasName ←
        if (← getLCtx).findFromUserName? cand |>.isSome then
          mkFreshUserName cand
        else
          pure cand
      acc := acc ++ [(n, mkIdent aliasName)]
  return acc

/-- Wrap `core` with `let a₀ := a; …` for each outer alias. -/
def Expectation.Macro.wrapAliases (aliases : List (Name × Ident)) (core : Term) : MacroM Term := do
  let mut result := core
  for (n, a) in aliases.reverse do
    let b := mkIdent n
    result ← `(let $a := $b; $result)
  pure result

open Lean.Elab.Term in
/-- Elaborate one `𝔼` form. `build` receives the unpacked body.
Threads outer aliases through `desugarProbRA` so nested aliasable `ℙ` / `𝔼` RA sugar
(anywhere under the body, including under `𝕍𝕒𝕣`/`ℂ𝕠𝕧`/`ℙ`) becomes observation form. -/
def Expectation.Macro.elabExpect (xs : Array Syntax) (body : Syntax)
    (build : Term → MacroM Term) : TermElabM Lean.Expr := do
  let aliases ← Expectation.Macro.mkOuterAliases xs
  let body' ← Lean.Elab.liftMacroM <| Expectation.Macro.desugarProbRA aliases body
  let mask ← Expectation.Macro.rebindMask xs body'
  let asFun ← Expectation.Macro.funBinderMask xs
  let nest := mkIdent `«integ»
  let unpacked ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest xs nest ⟨body'⟩ mask asFun
  let lam ← if mask.any id then
      `(fun $nest ↦ $unpacked)
    else
      `(fun _ ↦ $unpacked)
  let core ← Lean.Elab.liftMacroM <| build lam
  let wrapped ← Lean.Elab.liftMacroM <| Expectation.Macro.wrapAliases aliases core
  Lean.Elab.Term.elabTerm wrapped none

