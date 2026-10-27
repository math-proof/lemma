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
import Syntax.Probability.JointRv
open MeasureTheory
open scoped ProbabilityTheory


open Lean Elab Term Meta in
@[term_elab condIndepLeft] def elabCondIndepLeft : TermElab := fun stx _ => do
  match stx with
  | `(condIndepLeft% $x) =>
    let e ← Lean.Elab.Term.elabTerm x none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← whnfR (← instantiateMVars (← inferType e))
    match ty with
    | .forallE _ d b _ =>
      if d.isConstOf ``Nat && !b.hasLooseBVars && (← whnfR b).isForall then
        mkAppM ``Expectation.asRV #[e]
      else
        return e
    | _ => return e
  | _ => throwUnsupportedSyntax

