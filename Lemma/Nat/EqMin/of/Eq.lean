import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a = b)
  (x : ℝ) :
-- imply
  min a x = min b x := by
-- proof
  rw [h]


-- created on 2019-05-27
