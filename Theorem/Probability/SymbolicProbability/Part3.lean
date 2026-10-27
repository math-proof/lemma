import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv.Part3
import Instance.Probability.SymbolicProbability.Part3
open MeasureTheory


export Expectation (expectation)


/-- Unfolding rule for the Bochner instance (use `simp only [expectation_bochner]`). -/
@[simp] theorem expectation_bochner
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) (f : α → E) :
    expectation ν f = ∫ a, f a ∂ν :=
  rfl

