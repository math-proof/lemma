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
import Syntax.Probability.JointRv.Part3
open MeasureTheory
open scoped ProbabilityTheory


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

