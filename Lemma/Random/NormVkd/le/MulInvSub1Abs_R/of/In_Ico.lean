import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import Lemma.Random.NormWkd.le.Abs_R
open MeasureTheory PolicyGradient Random


/--
For `γ ∈ [0, 1)` the state value with a density policy is bounded: `‖Vkd θ γ x‖ ≤ (1 - γ)⁻¹ * |R|`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
-- given
  (h : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S) :
-- imply
  ‖M.Vkd θ γ x‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
-- proof
  apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h.1 h.2).mul_right |M.env.R|)
  intro k
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h.1]
  apply mul_le_mul_of_nonneg_left (NormWkd.le.Abs_R (M := M) θ k x) (pow_nonneg h.1 k)


-- created on 2026-10-07
