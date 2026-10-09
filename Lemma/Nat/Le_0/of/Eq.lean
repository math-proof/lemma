import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (hb : b ≤ 0)
  (h : a = b) :
-- imply
  a ≤ 0 := by
-- proof
  rw [h]
  exact hb


-- created on 2021-08-24
