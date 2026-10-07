import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The clamped reward is bounded by the reward bound: `‖rc z‖ ≤ |R|`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (z : ℝ × S × A) :
-- imply
  ‖M.rc z‖ ≤ |M.env.R| := by
-- proof
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_trans (neg_le_neg (le_abs_self _)) (le_max_left _ _),
    max_le (neg_le_abs _) ((min_le_left _ _).trans (le_abs_self _))⟩


-- created on 2026-10-07
