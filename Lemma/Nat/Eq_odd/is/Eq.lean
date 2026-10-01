import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ} :
-- imply
  n % 2 = 1 ↔ (-1 : ℝ) ^ n = -1 := by
-- proof
  constructor
  · intro h
    exact Odd.neg_one_zpow (Int.odd_iff.mpr h)
  · intro h
    by_contra hne
    rw [Even.neg_one_zpow (Int.even_iff.mpr (by omega))] at h
    norm_num at h


-- created on 2026-09-27
