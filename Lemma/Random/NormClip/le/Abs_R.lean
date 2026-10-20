import sympy.stats.policy_trajectory
import sympy.functions.elementary.miscellaneous


/--
The clamped reward is bounded by the reward bound: `‖clip ρ (-R) R‖ ≤ |R|`.
-/
@[path]
private lemma main
-- given
  (R ρ : ℝ) :
-- imply
  ‖clip ρ (-R) R‖ ≤ |R| := by
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


-- created on 2026-10-20
