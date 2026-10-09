import sympy.stats.policy_trajectory.continuous
import sympy.Basic
import Lemma.Random.NormWk.le.Abs_R
import Lemma.Random.Measurable_Wk.of.All_Measurable_Prob
import Lemma.Random.Summable_MulPowWk.of.In_Ico
open MeasureTheory PolicyGradient Random


/--
Bellman equation of the closed-form values on a general (e.g. continuous) state space:
`Vk θ γ x = ∑ u, π_θ(u | x) * Qk θ γ x u`.
Continuous-state counterpart of `Random.Vc.eq.Sum_MulProbQc.of.In_Ico`; `h₀` (measurability of the policy in the state)
makes the next-state integrals `∫ y, Wk θ k y ∂T(· | x, u)` meaningful, so that `∑'` and `∫` can be swapped.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ θ u, Measurable (fun x => M.pol.prob θ x u))
  (h₁ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S) :
-- imply
  M.Vk θ γ x = ∑ u, M.pol.prob θ x u * M.Qk θ γ x u := by
-- proof
  have := M.env.trans_markov
  have hb : ∀ k y, ‖γ ^ k * M.Wk θ k y‖ ≤ γ ^ k * |M.env.R| := fun k y => by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₁.1]
    apply mul_le_mul_of_nonneg_left (NormWk.le.Abs_R (M := M) θ k y) (pow_nonneg h₁.1 k)
  have hI : ∀ u, HasSum (fun k => γ ^ k * ∫ y, M.Wk θ k y ∂(M.env.trans (x, u)))
      (∫ y, M.Vk θ γ y ∂(M.env.trans (x, u))) := by
    intro u
    have hs : Summable fun k => ∫ y, ‖γ ^ k * M.Wk θ k y‖ ∂(M.env.trans (x, u)) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₁.1 h₁.2).mul_right |M.env.R|) fun k => ?_
      have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
        (f := fun y => ‖γ ^ k * M.Wk θ k y‖) (C := γ ^ k * |M.env.R|)
        (Filter.Eventually.of_forall fun y => by rw [norm_norm]; exact hb k y)
      simpa using h
    have h := hasSum_integral_of_summable_integral_norm (fun k => Integrable.of_bound
      ((Measurable_Wk.of.All_Measurable_Prob (M := M) h₀ θ k).const_mul _).aestronglyMeasurable
      (γ ^ k * |M.env.R|) (Filter.Eventually.of_forall (hb k))) hs
    simpa [integral_const_mul, Model.Vk] using h
  have hS : HasSum (fun k => γ ^ (k + 1) * M.Wk θ (k + 1) x)
      (γ * ∑ u, M.pol.prob θ x u * ∫ y, M.Vk θ γ y ∂(M.env.trans (x, u))) := by
    have h := (hasSum_sum (s := Finset.univ) fun u _ => ((hI u).mul_left (M.pol.prob θ x u))).mul_left γ
    refine (show (fun k => γ ^ (k + 1) * M.Wk θ (k + 1) x) = _ from funext fun k => ?_) ▸ h
    show γ ^ (k + 1) * ∑ u, M.pol.prob θ x u * ∫ y, M.Wk θ k y ∂(M.env.trans (x, u)) = _
    rw [Finset.mul_sum, Finset.mul_sum, pow_succ]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  unfold Model.Vk
  rw [(Summable_MulPowWk.of.In_Ico (M := M) h₁ θ x).tsum_eq_zero_add, hS.tsum_eq]
  show (γ ^ 0 * ∑ u, M.pol.prob θ x u * M.rk x u) + _ = _
  unfold Model.Qk Model.Vk
  simp only [pow_zero, one_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring


-- created on 2026-10-07
