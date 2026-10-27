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
import Class.Probability.JointRv
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

/-- Process-style reading of `Fun ℕ (Ω → α)` so Expectation binders / AsPathRV.path work. -/
@[reducible]
instance (priority := 1000) AsPathRV.funProcess {Ω α : Type*} :
    AsPathRV (Fun ℕ (Ω → α)) Ω (ℕ → α) where
  path f := fun ω t ↦ f.toFun t ω

