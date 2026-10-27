import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : y < x) :
-- imply
  y ≤ x :=
-- proof
  le_of_lt h


-- created on 2020-05-11
