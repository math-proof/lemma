import sympy.stats.policy_trajectory.advantage
import sympy.Basic
import Lemma.Random.AeNormR.le.Abs_R
import Lemma.Random.NormW.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma Vc_bdd [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (x : S) :
    ‖M.Vc θ γ x‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
  unfold Model.Vc
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right _) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
  exact mul_le_mul_of_nonneg_left (NormW.le.Abs_R (M := M) θ k x) (pow_nonneg hγ.1 k)

/--
Almost surely every temporal-difference residual `δ[j] = r[j] + γ * Vc(s[j+1]) - Vc(s[j])` is bounded by `deltaBound γ`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ j, ‖reward j ω + γ * M.Vc θ γ (state (j + 1) ω) - M.Vc θ γ (state j ω)‖ ≤
    M.deltaBound γ := by
-- proof
  filter_upwards [AeNormR.le.Abs_R (M := M) θ] with ω hr j
  calc _ ≤ ‖reward j ω‖ + ‖γ * M.Vc θ γ (state (j + 1) ω)‖ + ‖M.Vc θ γ (state j ω)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ M.deltaBound γ := by
        rw [norm_mul, Real.norm_of_nonneg h₀.1]
        exact add_le_add (add_le_add (hr j) (mul_le_mul_of_nonneg_left (Vc_bdd M θ h₀ _) h₀.1))
          (Vc_bdd M θ h₀ _)


-- created on 2026-10-06
