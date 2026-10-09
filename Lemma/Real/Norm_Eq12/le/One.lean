import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
The state indicator `1{z.2.1 = y}` of a stage `z = (r, s, a)` has norm at most `1`.
-/
@[path]
private lemma main
  [DecidableEq S]
-- given
  (y : S)
  (z : ℝ × S × A) :
-- imply
  ‖(if z.2.1 = y then (1:ℝ) else 0)‖ ≤ 1 := by
-- proof
  split_ifs <;> simp


-- created on 2026-10-06
