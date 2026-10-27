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
import Syntax.Probability.JointRv.Part2
open MeasureTheory
open scoped ProbabilityTheory


set_option quotPrecheck false in
/-- CondIndepFun sugar: `X ⟂ᵢ[π] Y | Z` is `CondIndepFun (σ(Z)) _ X Y π`.

Precedence 100 beats Mathlib’s `x ⟂ᵢ[π] y` (50) so the trailing `| z` is not left
behind. The proof of `Measurable Z` is found by `assumption` (a local `hz`) or `apply_assumption`
(e.g. `h : ∀ t, Measurable (s t)` for `Z = s (t + 1)`), or by `measurable_component` as a component
of a (∀-quantified) joint measurability hypothesis (e.g. `h : ∀ t, Measurable (r t, s t, a t)`).
If the left operand is a process
`ℕ → Ω → α`, such as the slice `r[t + 1:]`, it is read through `Expectation.asRV` as the
path-valued RV `fun ω k ↦ r (t + 1 + k) ω`; an ordinary RV `x : Ω → α` is left untouched. -/
notation:100 X:100 " ⟂ᵢ[" μ "] " Y:100 " | " Z:100 =>
  ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap Z inferInstance)
    (Measurable.comap_le (by
      first
      | assumption
      | apply_assumption
      | measurable_component : Measurable Z))
    (condIndepLeft% X) Y μ

