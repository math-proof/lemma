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
import Theorem.Probability.JointRv.Part2
open MeasureTheory
open scoped ProbabilityTheory


/-- Left operand of the `⟂ᵢ` sugar: a process `X : ℕ → Ω → α` (e.g. a slice `r[t + 1:]`) becomes
its path-valued RV `Expectation.asRV X = fun ω k ↦ X k ω`; any other term is returned unchanged
(syntactically, so `rw`/`simp` patterns on ordinary RVs keep matching). -/
syntax (name := condIndepLeft) "condIndepLeft% " term:max : term

