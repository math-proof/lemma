import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℤ} :
-- imply
  (if (0 : ℤ) = n % 2 then (1 : ℝ) else 0) = 1 - (if (1 : ℤ) = n % 2 then (1 : ℝ) else 0) := by
-- proof
  if h : n % 2 = 0 then
    rw [ite_eq_left h.symm, ite_eq_right (by omega)]
    norm_num
  else
    rw [ite_eq_right (Ne.symm h), ite_eq_left (by omega)]
    norm_num


-- created on 2023-05-22
