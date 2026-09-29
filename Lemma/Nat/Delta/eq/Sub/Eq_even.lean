import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℤ} :
-- imply
  (if (0 : ℤ) = n % 2 then (1 : ℝ) else 0) = 1 - (if (1 : ℤ) = n % 2 then (1 : ℝ) else 0) := by
-- proof
  by_cases h : n % 2 = 0
  · rw [if_pos h.symm, if_neg (by omega)]
    norm_num
  · rw [if_neg (Ne.symm h), if_pos (by omega)]
    norm_num


-- created on 2026-09-27
