import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n % 2 = 1) :
-- imply
  (-1 : ℝ) ^ n = -1 := by
-- proof
  exact Odd.neg_one_zpow (Int.odd_iff.mpr h)


-- created on 2019-10-12
