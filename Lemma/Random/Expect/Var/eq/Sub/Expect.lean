import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Law of total variance, rearranged: the gap between `𝔼[Y²]` and `𝔼[(𝔼[Y | m])²]` is
`Var[Y] - Var[𝔼[Y | m]]`.
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
  π[Y ^ 2] - π[(π[Y | m]) ^ 2] = variance Y π - variance (π[Y | m]) π := by
-- proof
  rw [variance_eq_sub h₁, variance_eq_sub (MemLp.condExp one_le_two h₁), integral_condExp (μ := π) h₀]
  ring


-- created on 2026-10-11
-- updated on 2026-10-17
