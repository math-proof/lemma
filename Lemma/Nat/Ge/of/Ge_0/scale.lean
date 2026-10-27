import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x t : ℝ}
-- given
  (hx : 0 ≤ x)
  (ht : 1 ≤ t) :
-- imply
  0 ≤ t * x := by
-- proof
  apply mul_nonneg _ hx
  linarith


-- created on 2019-06-14
