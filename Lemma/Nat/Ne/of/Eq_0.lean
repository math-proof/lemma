import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {n : ℤ}
-- given
  (h : n % 2 = 0) :
-- imply
  n % 2 ≠ 1 := by
-- proof
  omega


-- created on 2023-05-22
