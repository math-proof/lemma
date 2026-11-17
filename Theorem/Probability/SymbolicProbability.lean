import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Probability.Rv
import Instance.Probability.SymbolicProbability
open MeasureTheory


export Expectation (expectation)


/-- Unfolding rule for the `ENNReal` instance (use `simp only [expectation_ennreal]`). -/
@[simp] theorem expectation_ennreal
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ENNReal) :
    expectation ν f = ∫⁻ a, f a ∂ν :=
  rfl

/-- Unfolding rule for the `ℝ` instance (use `simp only [expectation_real]`). -/
@[simp] theorem expectation_real
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ℝ) :
    expectation ν f = ∫ a, f a ∂ν :=
  rfl

/-- Unfolding rule for the Bochner instance (use `simp only [expectation_bochner]`). -/
@[simp] theorem expectation_bochner
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) (f : α → E) :
    expectation ν f = ∫ a, f a ∂ν :=
  rfl
