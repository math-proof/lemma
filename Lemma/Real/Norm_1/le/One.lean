import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


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
-- updated on 2026-11-15
