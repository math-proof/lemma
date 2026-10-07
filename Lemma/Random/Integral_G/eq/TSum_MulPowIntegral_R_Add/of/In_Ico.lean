import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.AeR.eq.Rc
import Lemma.Random.NormRc.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
For `γ ∈ [0, 1)`: `𝔼[G[t] | B] = ∑' k, γ ^ k * 𝔼[r[t+k] | B]`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (B : Set (ℕ → ℝ × S × A))
  (t : ℕ) :
-- imply
  ∫ ω, G γ t ω ∂(M θ)[|B] = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|B] := by
-- proof
  if hB : M θ B = 0 then
    simp [cond_eq_zero_of_meas_eq_zero hB]
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    have hae : ∀ᵐ ω ∂(M θ)[|B], ∀ k, ‖r k ω‖ ≤ |M.env.R| := by
      apply cond_absolutelyContinuous.ae_le
      exact ae_all_iff.2 fun k => (AeR.eq.Rc (M := M) θ k).mono fun ω h => by rw [h]; exact NormRc.le.Abs_R (M := M) _
    have hm : ∀ k, Measurable (r (S := S) (A := A) k) := fun k =>
      measurable_fst.comp (measurable_pi_apply k)
    have hF : ∀ k, Integrable (fun ω => γ ^ k * r (t + k) ω) (M θ)[|B] := fun k =>
      Integrable.of_bound ((hm (t + k)).const_mul (γ ^ k)).aestronglyMeasurable (γ ^ k * |M.env.R|)
        (hae.mono fun ω h => by
          rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
          exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hγ.1 k))
    have hS : Summable (fun k => ∫ ω, ‖γ ^ k * r (t + k) ω‖ ∂(M θ)[|B]) := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) (fun k => ?_)
        ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|)
      have hb : ∀ᵐ ω ∂(M θ)[|B], ‖‖γ ^ k * r (t + k) ω‖‖ ≤ γ ^ k * |M.env.R| :=
        hae.mono fun ω h => by
          rw [norm_norm, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
          exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hγ.1 k)
      have := norm_integral_le_of_norm_le_const hb
      simp only [probReal_univ, mul_one] at this
      exact (Real.le_norm_self _).trans this
    simp only [G]
    rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
    congr 1; funext k
    exact integral_const_mul _ _


-- created on 2026-10-07
