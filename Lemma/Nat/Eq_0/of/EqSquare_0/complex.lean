import Mathlib.Basic.Complex.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : x ^ 2 = 0) :
-- imply
  x = 0 := by
-- proof
  apply mul_self_eq_zero.mp
  simpa [pow_two] using h


-- created on 2018-11-11
