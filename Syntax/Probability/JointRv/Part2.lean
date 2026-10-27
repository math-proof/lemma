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
import Def.Probability.JointRv.Part4
open MeasureTheory
open scoped ProbabilityTheory


open Lean Meta Elab Tactic in
/-- `measurable_component` closes a goal `Measurable z` from a local (possibly ∀-quantified)
measurability hypothesis:
* joint / product RVs, e.g. `h : ∀ t, Measurable (r t, s t, a t)` (via `Function.coeProdPi*` /
  `JointRandomSymbol`): tries `(h …).fst`, `(h …).snd`, and the two-step projections;
* closed slices, e.g. `hx : Measurable x[:n]` proving `Measurable x[i]` for `i : Fin n`, via
  `(measurable_pi_apply i).comp hx`;
* the same shapes wrapped in `Fact`, e.g. `[hx : Fact (Measurable x[:n])]`, via `Fact.out`.

Used by the `⟂ᵢ` sugar after `assumption` / `apply_assumption`. -/
elab "measurable_component" : tactic => withMainContext do
  let measurableProofFrom? (ldecl : LocalDecl) : MetaM (Option (Array Expr × Expr × Bool)) := do
    let (xs, _, body) ← forallMetaTelescope (← instantiateMVars ldecl.type)
    if body.isAppOf ``Measurable then
      return some (xs, mkAppN ldecl.toExpr xs, false)
    if body.isAppOf ``Fact then
      let p := body.appArg!
      unless p.isAppOf ``Measurable do return none
      -- `Fact.out` is instance-implicit in the `Fact` arg; use the structure projection
      let pf ← mkProjection (mkAppN ldecl.toExpr xs) `out
      return some (xs, pf, true)
    return none
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let paths : List (List Name) :=
    [[``Measurable.fst], [``Measurable.snd],
     [``Measurable.snd, ``Measurable.fst], [``Measurable.snd, ``Measurable.snd],
     [``Measurable.fst, ``Measurable.fst], [``Measurable.fst, ``Measurable.snd]]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    -- product / joint projections
    for path in paths do
      let s ← saveState
      try
        let some (_xs, base, _isFact) ← measurableProofFrom? ldecl |
          throwError "not a measurability hypothesis"
        let mut pf := base
        for n in path do
          pf ← mkAppM n #[pf]
        if ← isDefEq (← inferType pf) target then
          let pf' ← instantiateMVars pf
          unless pf'.hasExprMVar do
            goal.assign pf'
            replaceMainGoal []
            return
        s.restore
      catch _ => s.restore
    -- closed slice → index: `(measurable_pi_apply i).comp h`
    let s ← saveState
    try
      let some (xs, base, isFact) ← measurableProofFrom? ldecl |
        throwError "not a measurability hypothesis"
      -- skip ∀-quantified hyps here; only bare `Measurable (·[:n])` / `Fact (Measurable …)`
      unless xs.isEmpty do throwError "quantified"
      if isFact then
        -- Delab of `Fact.out` drops the instance arg and gets stuck; use `hx.out`
        evalTactic (← `(tactic| exact (measurable_pi_apply _).comp $(mkIdent ldecl.userName).out))
      else
        let hStx ← PrettyPrinter.delab base
        evalTactic (← `(tactic| exact (measurable_pi_apply _).comp $hStx))
      return
    catch _ => s.restore
  throwError "measurable_component: the goal is not a component of a joint measurability hypothesis"

