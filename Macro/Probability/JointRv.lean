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
import Def.Probability.JointRv.Part6
open MeasureTheory
open scoped ProbabilityTheory


-- `f =ᵐ[μ] g` (Mathlib's `Filter.EventuallyEq (ae μ) f g`) with both sides read through `rv%[μ]`,
-- e.g. `V t (s t) =ᵐ[π] …` is `(fun ω ↦ V t (s t ω)) =ᵐ[π] …`.
macro_rules
  | `($f =ᵐ[$μ] $g) => `(Filter.EventuallyEq (MeasureTheory.ae $μ) (rv%[$μ] $f) (rv%[$μ] $g))

