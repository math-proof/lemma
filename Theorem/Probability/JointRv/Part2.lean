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
import Def.Probability.JointRv.Part3
open MeasureTheory
open scoped ProbabilityTheory


@[simp] theorem Expectation.asRV_function {Ω α : Type*} (f : Ω → α) :
    Expectation.asRV f = f :=
  rfl

@[simp] theorem Expectation.asRV_process {Ω α : Type*} (X : ℕ → Ω → α) :
    Expectation.asRV X = fun ω t ↦ X t ω :=
  rfl

@[simp] theorem Expectation.asRV_fun {Ω α : Type*} (f : Fun ℕ (Ω → α)) :
    Expectation.asRV f = fun ω t ↦ f.toFun t ω :=
  rfl

