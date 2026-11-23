module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional
public import Class.Probability.JointRv

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory


/-- Ordinary random variable: binder is already `Ω → α`. -/
@[reducible]
instance (priority := 100) AsPathRV.ofFunction {Ω α : Type*} : AsPathRV (Ω → α) Ω α where
  path f := f

/-- Time-indexed process: binder `X` becomes the path-valued RV `fun ω t ↦ X t ω`. -/
@[reducible]
instance (priority := 1000) AsPathRV.process {Ω α : Type*} :
    AsPathRV (ℕ → Ω → α) Ω (ℕ → α) where
  path f := fun ω t ↦ f t ω

