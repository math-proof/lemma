import sympy.stats.policy_trajectory.gradient
import Lemma.Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
the state-value function is bounded by the discounted reward bound, at every `t` and `x`
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S) :
-- imply
  ‖M.V r s θ γ t x‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₀.2])) (abs_nonneg _)
  rw [M.V_eq_integral r s]
  show ‖∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x}]‖ ≤ _
  have hae : ∀ᵐ ω ∂(M θ)[|s t ⁻¹' {x}], ‖((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    cond_absolutelyContinuous.ae_le ((AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ t).mono fun ω h => h.2)
  if hB : M θ (s t ⁻¹' {x}) = 0 then
    rw [cond_eq_zero_of_meas_eq_zero hB]
    simpa using hq
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    simpa using norm_integral_le_of_norm_le_const hae


-- created on 2026-10-06
