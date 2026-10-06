import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
Bellman equation of the time-free closed-form values: `Vc θ γ x = ∑ u, π_θ(u | x) * Qc θ γ x u`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (x : S) :
-- imply
  M.Vc θ γ x = ∑ u, M.pol.prob θ x u * M.Qc θ γ x u := by
-- proof
  unfold Model.Qc Model.Vc
  rw [v_closed M θ h₀ x, W_zero M θ (rc_sm M) (rc_bdd M) x, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring


-- created on 2026-10-06
