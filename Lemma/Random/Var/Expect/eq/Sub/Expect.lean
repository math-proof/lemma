import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Variance of a conditional expectation:
`Var(𝔼[Y | m]) = 𝔼[(𝔼[Y | m])²] - (𝔼[Y])²`.
-/
@[path]
private lemma main
  [mΩ : MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m : MeasurableSpace Ω}
  {Y : Ω → ℝ}
-- given
  (h₀ : m ≤ mΩ)
  (h₁ : MemLp Y 2 π) :
-- imply
  variance (π[Y | m]) π = π[(π[Y | m]) ^ 2] - π[Y] ^ 2 := by
-- proof
  rw [variance_eq_sub (MemLp.condExp one_le_two h₁), integral_condExp (μ := π) h₀]


-- created on 2026-10-11
-- updated on 2026-10-17
