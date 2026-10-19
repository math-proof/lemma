import sympy.stats.policy_trajectory
import sympy.functions.elementary.miscellaneous
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The clamped reward is bounded by the reward bound:
`‖clip z.1 (-R) R‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (z : ℝ × S × A) :
-- imply
  ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| := by
-- proof
  rw [Real.norm_eq_abs, abs_le, clip]
  constructor
  ·
    apply le_min
    ·
      apply (neg_le_neg (le_abs_self _)).trans
      apply le_max_right
    ·
      apply neg_abs_le
  ·
    apply (min_le_right _ _).trans
    apply le_abs_self


-- created on 2026-10-07
-- updated on 2026-10-12
