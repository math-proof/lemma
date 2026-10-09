import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
An indicator has norm at most `1`: `‖1{p z}‖ ≤ 1`.
-/
@[path]
private lemma main
  {p : α → Prop} [DecidablePred p]
-- given
  (z : α) :
-- imply
  ‖(if p z then (1:ℝ) else 0)‖ ≤ 1 := by
-- proof
  split_ifs <;> simp


-- created on 2026-10-07
