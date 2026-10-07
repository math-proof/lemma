import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
Almost surely every reward of the trajectory model is bounded by the reward bound: `∀ k, ‖r[k]‖ ≤ |R|`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, ‖r k ω‖ ≤ |M.env.R| := by
-- proof
  rw [ae_all_iff]
  exact fun k => (r_ae M θ k).mono fun ω h => by rw [h]; exact rc_bdd M _


-- created on 2026-10-06
