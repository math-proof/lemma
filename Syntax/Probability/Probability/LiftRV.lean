module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional
public import Def.Probability.SymbolicProbability

public meta section

open MeasureTheory
open scoped ProbabilityTheory


open Lean in
/-- Identifiers occurring in a syntax tree (deduplicated, first occurrence first). -/
partial def LiftRV.idents (stx : Syntax) (acc : Array Ident := #[]) : Array Ident :=
  if stx.isIdent then
    if acc.any (·.getId == stx.getId) then acc else acc.push ⟨stx⟩
  else
    stx.getArgs.foldl (fun acc a => LiftRV.idents a acc) acc

open Lean Meta in
/-- `some false` if `ty` is `Ω → α` (a random variable on `Ω`), `some true` if it is an indexed family
`ℕ → Ω → α` or `Fin n → Ω → α` (a process), `none` otherwise.
A process is lifted by `let s := fun k ↦ s k ω` (`s t` beta-reduces to `s t ω`). -/
def LiftRV.kind (Ω ty : Expr) : MetaM (Option Bool) := withNewMCtxDepth do
  match ← whnf ty with
  | .forallE _ d b _ =>
    if b.hasLooseBVars then return none
    if ← isDefEq d Ω then return some false
    let d ← whnf d
    unless d.isConstOf ``Nat || d.isAppOfArity ``Fin 1 do return none
    match ← whnf b with
    | .forallE _ d' b' _ =>
      if !b'.hasLooseBVars && (← isDefEq d' Ω) then return some true else return none
    | _ => return none
  | _ => return none

open Lean Elab Term Meta in
def LiftRV.lift (μ x : Term) (expectedType? : Option Expr) : TermElabM Expr := withFreshMacroScope do
  let μe ← Lean.Elab.Term.elabTerm μ none
  let μty ← whnf (← instantiateMVars (← inferType μe))
  unless μty.isAppOfArity ``MeasureTheory.Measure 2 do throwError "rv%: {μe} is not a measure"
  let Ω := μty.appFn!.appArg!
  -- `proc` marks a time-indexed family.
  let mut binds : Array (Ident × Bool) := #[]
  for id in LiftRV.idents x do
    let some (fv, []) ← resolveLocalName id.getId | continue
    let ty ← instantiateMVars (← inferType fv)
    if let some proc ← LiftRV.kind Ω ty then
      binds := binds.push (id, proc)
  if binds.isEmpty then throwError "rv%: no random variable on {Ω} to lift in {x}"
  let mut body : Term := x
  for (id, proc) in binds.reverse do
    body ← if proc then `(let $id := fun k ↦ $id k ω; $body)
      else `(let $id := $id ω; $body)
  let e ← Lean.Elab.Term.elabTerm (← `(fun (ω : $(← exprToSyntax Ω)) ↦ $body)) expectedType?
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let e ← lambdaBoundedTelescope e 1 fun xs b => do
    let mut b := b
    for _ in binds do
      match b with
      | .letE _ _ v b' _ => b := b'.instantiateBetaRevRange 0 1 #[v]
      | _ => throwError "rv%: unexpected elaboration result {b}"
    mkLambdaFVars xs b
  match e with
  | .lam _ t b bi => return .lam `ω t b bi
  | e => return e


syntax (name := liftRV) "rv%[" term "] " term:max : term


open Lean Elab Term Meta in
@[term_elab liftRV] def elabLiftRV : TermElab := fun stx expectedType? => do
  match stx with
  | `(rv%[$μ] $x) =>
    let saved ← saveState
    try
      withoutErrToSorry (Lean.Elab.Term.elabTerm x expectedType?)
    catch ex =>
      if let .internal id _ := ex then
        if id == postponeExceptionId then throw ex
      let failed ← saveState
      saved.restore
      try
        LiftRV.lift μ x expectedType?
      catch _ =>
        failed.restore
        throw ex
  | _ => throwUnsupportedSyntax


macro_rules
  | `($f =ᵐ[$μ] $g) => `(Filter.EventuallyEq (MeasureTheory.ae $μ) (rv%[$μ] $f) (rv%[$μ] $g))
