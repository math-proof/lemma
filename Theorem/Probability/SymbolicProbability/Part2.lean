import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
import Instance.Probability.SymbolicProbability.Part2
open MeasureTheory


export Expectation (expectation)


/-- Unfolding rule for the `ℝ` instance (use `simp only [expectation_real]`). -/
@[simp] theorem expectation_real
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ℝ) :
    expectation ν f = ∫ a, f a ∂ν :=
  rfl

