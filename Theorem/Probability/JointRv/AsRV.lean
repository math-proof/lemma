module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional
public import Def.Probability.SymbolicProbability
public import Def.Probability.Expectation
open MeasureTheory
open scoped ProbabilityTheory

public section


@[simp] theorem Expectation.asRV_function {Ω α : Type*} (f : Ω → α) :
    Expectation.asRV f = f :=
  rfl

@[simp] theorem Expectation.asRV_process {Ω α : Type*} (X : ℕ → Ω → α) :
    Expectation.asRV X = fun ω t ↦ X t ω :=
  rfl
