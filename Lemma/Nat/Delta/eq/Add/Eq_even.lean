import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ} :
-- imply
  (if (0 : ℤ) = n % 2 then (1 : ℝ) else 0) = (1 + (-1 : ℝ) ^ n) / 2 := by
-- proof
  have key : (-1 : ℝ) ^ n = if n % 2 = 0 then 1 else -1 := by
    split_ifs with h
    · exact Even.neg_one_zpow (Int.even_iff.mpr h)
    · exact Odd.neg_one_zpow (Int.odd_iff.mpr (by omega))
  rw [key]
  by_cases h : n % 2 = 0
  · rw [if_pos h.symm, if_pos h]
    norm_num
  · rw [if_neg (Ne.symm h), if_neg h]
    norm_num


-- created on 2023-05-22
