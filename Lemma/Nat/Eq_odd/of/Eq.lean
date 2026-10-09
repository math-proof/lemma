import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {n : ℤ}
-- given
  (h : (-1 : ℝ) ^ n = -1) :
-- imply
  n % 2 = 1 := by
-- proof
  by_contra hne
  rw [Even.neg_one_zpow (Int.even_iff.mpr (by omega))] at h
  norm_num at h


-- created on 2019-10-12
