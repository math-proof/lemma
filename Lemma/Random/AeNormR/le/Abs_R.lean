import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.MEqR_Rc
import Lemma.Random.NormRc.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Almost surely every reward of the trajectory model is bounded by the reward bound: `∀ k, ‖r[k]‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, ‖r k ω‖ ≤ |M.env.R| := by
-- proof
  rw [ae_all_iff]
  exact fun k => (MEqR_Rc h₁ (M := M) θ k).mono fun ω h => by rw [h]; exact NormRc.le.Abs_R (M := M) _


-- created on 2026-10-06
