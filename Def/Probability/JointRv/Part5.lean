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
import Notation.Probability.JointRv
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
/-- `Fun ℕ (β → γ)` (a `Fun` process such as `Fun ℕ (Ω → S)`). The value path is re-wrapped with
`Fun.mk`, so `s[t]` stays `Fun` indexing and does not need `GetElem` on bare functions. -/
def LiftRV.isFunProcess (ty : Expr) : MetaM Bool := do
  match ← whnf ty with
  | .app (.app (.const n _) ι) α =>
    let ι ← whnf ι
    unless n == ``Fun && ι.isConstOf ``Nat do return false
    match ← whnf α with
    | .forallE _ _ b _ => return !b.hasLooseBVars
    | _ => return false
  | _ => return false

open Lean Meta in
/-- `some false` if `ty` is `Ω → α` (a random variable on `Ω`), `some true` if it is an indexed family
`ℕ → Ω → α`, `Fin n → Ω → α`, or `Fun ℕ (Ω → α)` (a process), `none` otherwise.
A bare process is lifted by `let s := fun k ↦ s k ω` (`s t` beta-reduces to `s t ω`).
A `Fun` process is lifted by `let s := Fun.mk (fun k ↦ s k ω)`, so `s[t]` is `Fun` indexing. -/
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
  | .app (.app (.const n _) ι) α =>
    let ι ← whnf ι
    unless n == ``Fun && ι.isConstOf ``Nat do return none
    match ← whnf α with
    | .forallE _ d b _ =>
      if !b.hasLooseBVars && (← isDefEq d Ω) then return some true else return none
    | _ => return none
  | _ => return none

open Lean Elab Term Meta in
/-- Fallback of `rv%[μ] x`: elaborate `fun ω ↦ let s := fun k ↦ s k ω; …; x` (`let x := x ω` for a plain
random variable `x`) for the local random variables / processes on `Ω` (from `μ : Measure Ω`) named in
`x`, then inline exactly these `let`s (beta-reducing `(fun k ↦ s k ω) t` to `s t ω`), so the result is
syntactically the hand-written `fun ω ↦ …`. -/
def LiftRV.lift (μ x : Term) (expectedType? : Option Expr) : TermElabM Expr := withFreshMacroScope do
  let μe ← Lean.Elab.Term.elabTerm μ none
  let μty ← whnf (← instantiateMVars (← inferType μe))
  unless μty.isAppOfArity ``MeasureTheory.Measure 2 do throwError "rv%: {μe} is not a measure"
  let Ω := μty.appFn!.appArg!
  -- `(proc, funProcess)`: `proc` is a time-indexed family; `funProcess` is `Fun ℕ (· → ·)`.
  let mut binds : Array (Ident × Bool × Bool) := #[]
  for id in LiftRV.idents x do
    let some (fv, []) ← resolveLocalName id.getId | continue
    let ty ← instantiateMVars (← inferType fv)
    if let some proc ← LiftRV.kind Ω ty then
      binds := binds.push (id, proc, ← LiftRV.isFunProcess ty)
  if binds.isEmpty then throwError "rv%: no random variable on {Ω} to lift in {x}"
  let mut body : Term := x
  for (id, proc, funProcess) in binds.reverse do
    body ← if funProcess then `(let $id := Fun.mk (fun k ↦ $id k ω); $body)
      else if proc then `(let $id := fun k ↦ $id k ω; $body)
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

