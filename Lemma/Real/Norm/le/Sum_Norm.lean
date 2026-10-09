import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Each value of a function on a finite type is bounded by the sum of all norms: `‖h y‖ ≤ ∑ y', ‖h y'‖`.
-/
@[path]
private lemma main
  [Fintype S]
-- given
  (h : S → ℝ)
  (y : S) :
-- imply
  ‖h y‖ ≤ ∑ y', ‖h y'‖ := by
-- proof
  exact Finset.single_le_sum (f := fun y' => ‖h y'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)


-- created on 2026-10-07
