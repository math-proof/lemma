import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {n : ℤ}
-- given
  (h : n % 2 = 1) :
-- imply
  n % 2 ≠ 0 := by
-- proof
  omega


-- created on 2020-01-27
