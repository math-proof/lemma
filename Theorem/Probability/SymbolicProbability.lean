import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
import Instance.Probability.SymbolicProbability
open MeasureTheory


export Expectation (expectation)


/-- Unfolding rule for the `ENNReal` instance (use `simp only [expectation_ennreal]`). -/
@[simp] theorem expectation_ennreal
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ENNReal) :
    expectation ν f = ∫⁻ a, f a ∂ν :=
  rfl

