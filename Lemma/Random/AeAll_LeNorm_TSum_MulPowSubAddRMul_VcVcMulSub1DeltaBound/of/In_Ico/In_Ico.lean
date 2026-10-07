import sympy.stats.policy_trajectory.advantage
import sympy.Basic
import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
Almost surely the `c`-discounted sums of temporal-difference residuals are bounded, uniformly in `t`:
`‖∑' k, c ^ k * δ[t + k]‖ ≤ (1 - c)⁻¹ * deltaBound γ`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ c : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : c ∈ Set.Ico 0 1) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ t, ‖∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
    M.Vc θ γ (s (t + k) ω))‖ ≤ (1 - c)⁻¹ * M.deltaBound γ := by
-- proof
  filter_upwards [Random.AeNormSub.le.DeltaBound.of.In_Ico (M := M) θ h₀] with ω h t
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₁.1 h₁.2).mul_right _) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h₁.1]
  exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₁.1 k)


-- created on 2026-10-06
