import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b n : ℝ}
-- given
  (h : a + b > n) :
-- imply
  min a (n - b) + min b (n - a) < n := by
-- proof
  rw [min_eq_right (by linarith), min_eq_right (by linarith)]
  linarith


-- created on 2022-07-12
