import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a = b)
  (x : ℝ) :
-- imply
  max a x = max b x := by
-- proof
  rw [h]


-- created on 2026-09-27
