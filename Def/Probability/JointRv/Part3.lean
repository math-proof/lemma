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
import Theorem.Probability.JointRv
open MeasureTheory
open scoped ProbabilityTheory


/--
Transparent binder coercion used by the `𝔼` macro.

Reducible so that for an ordinary RV `x : Ω → α` one has `Expectation.asRV x = x`
(definitionally), and proofs that rewrite with `π.map x` keep working. For a process
`X : ℕ → Ω → α`, this is the path `fun ω t ↦ X t ω`.
-/
@[reducible, inline]
def Expectation.asRV {X : Type*} {Ω α : Type*} [AsPathRV X Ω α] (x : X) : Ω → α :=
  AsPathRV.path x

