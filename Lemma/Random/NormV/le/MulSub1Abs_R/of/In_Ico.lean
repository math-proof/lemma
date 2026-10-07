import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
the state-value function is bounded by the discounted reward bound, at every `t` and `x`
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (x : S) :
-- imply
  ‖M.V θ γ t x‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
-- proof
  have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₀.2])) (abs_nonneg _)
  rw [V_eq_integral]
  have hae : ∀ᵐ ω ∂(M θ)[|s t ⁻¹' {x}], ‖G γ t ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    cond_absolutelyContinuous.ae_le ((Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) θ h₀ t).mono fun ω h => h.2)
  if hB : M θ (s t ⁻¹' {x}) = 0 then
    rw [cond_eq_zero_of_meas_eq_zero hB]
    simpa using hq
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    simpa using norm_integral_le_of_norm_le_const hae


-- created on 2026-10-06
