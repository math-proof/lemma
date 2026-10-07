import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.AeR.eq.Rc
import Lemma.Random.NormRc.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


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
  exact fun k => (AeR.eq.Rc (M := M) θ k).mono fun ω h => by rw [h]; exact NormRc.le.Abs_R (M := M) _


-- created on 2026-10-06
