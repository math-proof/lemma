import sympy.stats.policy_trajectory
import sympy.stats.cond_expectation
import sympy.stats.hidden_markov_sequence
import sympy.core.power
import sympy.vector.Basic
import sympy.Basic
import Lemma.Random.MEqR_Rc
import Lemma.Random.NormRc.le.Abs_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Linearity of conditional expectation through the infinite discounted sum: for `γ ∈ [0, 1)` and any event
`y = «y.bvar»` of the trajectory, the conditional expectation of the discounted return equals the discounted sum of
the conditional expected rewards,
`𝔼[(γ ^ id) @ r[t:] | y = «y.bvar»] = (γ ^ id) @ (k ↦ 𝔼[r[t+k] | y = «y.bvar»])`, where `u @ v = ∑' k, u k * v k`
(so the left side is `𝔼[G[t] | y = «y.bvar»]`, `G[t] = ∑' k, γ ^ k * r[t+k]`).
(Dominated convergence: the rewards are a.s. bounded by `|R|`.)
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (y : (ℕ → ℝ × S × A) → β)
  («y.bvar» : β)
  (t : ℕ) :
-- imply
  𝔼[reward : M θ]((γ ^ (id : ℕ → ℕ)) @ reward[t:] | y = «y.bvar») = (γ ^ (id : ℕ → ℕ)) @ fun k => 𝔼[reward : M θ](reward (t + k) | y = «y.bvar») := by
-- proof
  have hr : Measurable (fun ω k ↦ reward (S := S) (A := A) k ω) := measurable_pi_lambda _ fun k => measurable_fst.comp (measurable_pi_apply k)
  have h : ∀ k, 𝔼[reward : M θ](reward (t + k) | y = «y.bvar») = ∫ ω, reward (t + k) ω ∂(M θ)[|y ⁻¹' {«y.bvar»}] := fun k =>
    Expectation.condEvent_eq_integral hr.aemeasurable (measurable_pi_apply (t + k))
  simp only [h]
  simp only [Expectation.asRV_process]
  have hG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  rw [Expectation.condEvent_eq_integral hr.aemeasurable hG]
  show ∫ ω, ∑' k, γ ^ k * reward (t + k) ω ∂(M θ)[|y ⁻¹' {«y.bvar»}] = ∑' k, γ ^ k * ∫ ω, reward (t + k) ω ∂(M θ)[|y ⁻¹' {«y.bvar»}]
  generalize y ⁻¹' {«y.bvar»} = B
  if hB : M θ B = 0 then
    simp [cond_eq_zero_of_meas_eq_zero hB]
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    have hae : ∀ᵐ ω ∂(M θ)[|B], ∀ k, ‖reward k ω‖ ≤ |M.env.R| := by
      apply cond_absolutelyContinuous.ae_le
      exact ae_all_iff.2 fun k => (MEqR_Rc (M := M) θ k).mono fun ω h => by rw [h]; exact NormRc.le.Abs_R (M := M) _
    have hm : ∀ k, Measurable (reward (S := S) (A := A) k) := fun k =>
      measurable_fst.comp (measurable_pi_apply k)
    have hF : ∀ k, Integrable (fun ω => γ ^ k * reward (t + k) ω) (M θ)[|B] := fun k =>
      Integrable.of_bound ((hm (t + k)).const_mul (γ ^ k)).aestronglyMeasurable (γ ^ k * |M.env.R|)
        (hae.mono fun ω h => by
          rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
          exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hγ.1 k))
    have hS : Summable (fun k => ∫ ω, ‖γ ^ k * reward (t + k) ω‖ ∂(M θ)[|B]) := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) (fun k => ?_)
        ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|)
      have hb : ∀ᵐ ω ∂(M θ)[|B], ‖‖γ ^ k * reward (t + k) ω‖‖ ≤ γ ^ k * |M.env.R| :=
        hae.mono fun ω h => by
          rw [norm_norm, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
          exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hγ.1 k)
      have := norm_integral_le_of_norm_le_const hb
      simp only [probReal_univ, mul_one] at this
      exact (Real.le_norm_self _).trans this
    rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
    congr 1; funext k
    exact integral_const_mul _ _


-- created on 2026-10-07
