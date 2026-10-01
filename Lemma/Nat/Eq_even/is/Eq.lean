import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ} :
-- imply
  n % 2 = 0 ↔ (-1 : ℝ) ^ n = 1 := by
-- proof
  constructor
  · intro h
    exact Even.neg_one_zpow (Int.even_iff.mpr h)
  · intro h
    by_contra hne
    rw [Odd.neg_one_zpow (Int.odd_iff.mpr (by omega))] at h
    norm_num at h


-- created on 2019-10-11
