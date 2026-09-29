import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n % 2 = 0) :
-- imply
  (-1 : ℝ) ^ n = 1 := by
-- proof
  exact Even.neg_one_zpow (Int.even_iff.mpr h)


-- created on 2026-09-27
