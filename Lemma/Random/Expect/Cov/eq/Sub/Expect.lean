import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
Conditional covariance decomposition:
`𝔼[X Y] - 𝔼[𝔼[X | m] 𝔼[Y | m]] = cov[X, Y] - cov[𝔼[X | m], 𝔼[Y | m]]`.
-/
@[path]
private lemma main
  [mΩ : MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m : MeasurableSpace Ω}
  {X Y : Ω → ℝ}
-- given
  (h₀ : m ≤ mΩ)
  (h₁ : MemLp X 2 π)
  (h₂ : MemLp Y 2 π) :
-- imply
  ∫ ω, X ω * Y ω ∂π - ∫ ω, condExp m π X ω * condExp m π Y ω ∂π =
    covariance X Y π - covariance (condExp m π X) (condExp m π Y) π := by
-- proof
  rw [covariance_eq_sub h₁ h₂,
    covariance_eq_sub (MemLp.condExp one_le_two h₁) (MemLp.condExp one_le_two h₂),
    integral_condExp (μ := π) h₀, integral_condExp (μ := π) h₀]
  simp [Pi.mul_apply]


-- created on 2023-04-09
-- updated on 2026-10-26
