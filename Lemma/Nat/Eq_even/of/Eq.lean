import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {n : ℤ}
-- given
  (h : (-1 : ℝ) ^ n = 1) :
-- imply
  n % 2 = 0 := by
-- proof
  by_contra hne
  rw [Odd.neg_one_zpow (Int.odd_iff.mpr (by omega))] at h
  norm_num at h


-- created on 2019-10-10
