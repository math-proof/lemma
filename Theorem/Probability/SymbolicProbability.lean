module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.EReal.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Class.Probability.Rv
public import Instance.Probability.SymbolicProbability
open MeasureTheory


public section

export Expectation (expectation)


/-- Unfolding rule for the `ENNReal` instance (use `simp only [expectation_ennreal]`). -/
@[simp] public theorem expectation_ennreal
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ENNReal) :
    expectation ν f = ∫⁻ a, f a ∂ν :=
  rfl

/-- Unfolding rule for the `ℝ` instance (use `simp only [expectation_real]`). -/
@[simp] public theorem expectation_real
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ℝ) :
    expectation ν f = ∫ a, f a ∂ν :=
  rfl

/-- Unfolding rule for the Bochner instance (use `simp only [expectation_bochner]`). -/
@[simp] public theorem expectation_bochner
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) (f : α → E) :
    expectation ν f = ∫ a, f a ∂ν :=
  rfl
