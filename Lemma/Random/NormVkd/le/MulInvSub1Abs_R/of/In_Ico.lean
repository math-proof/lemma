import Lemma.Random.NormWkd.le.Abs_R
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
For `γ ∈ [0, 1)` the state value with a density policy is bounded: `‖V0 θ γ x‖ ≤ (1 - γ)⁻¹ * |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
-- given
  (h : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (sₜ : 𝒮) :
-- imply
  ‖M.V0 θ γ sₜ‖ ≤ (1 - γ)⁻¹ * |M.R| := by
-- proof
  unfold Model.V0
  apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h.1 h.2).mul_right |M.R|)
  intro k
  rw [norm_mul, norm_pow, Real.norm_of_nonneg h.1]
  apply mul_le_mul_of_nonneg_left (NormWkd.le.Abs_R (M := M) θ k sₜ) (pow_nonneg h.1 k)


-- created on 2026-10-07
-- updated on 2026-11-17