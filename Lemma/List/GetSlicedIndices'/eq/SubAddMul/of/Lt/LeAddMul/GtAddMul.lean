import Lemma.List.EqLengthGetSlicedIndices'.of.LeSubAddMul.GtSubAddMul
open List


@[main]
private lemma main
  {j' : Fin d}
-- given
  (h_stop : n * d + j > j + j')
  (h_start : n * d + j ≤ N)
  (h_i : i < n) :
-- imply
  (Nat.sliced_indices' h_stop h_start (Nat.Gt_0 j'))[i]'(by grind [EqLengthGetSlicedIndices'.of.LeSubAddMul.GtSubAddMul h_stop h_start]) = (n - i) * d + j - 1 := by
-- proof
  induction n generalizing i j with
  | zero =>
    simp
    linarith
  | succ n ih =>
    unfold Nat.sliced_indices'
    split_ifs with h_start?
    ·
      match i with
      | 0 =>
        simp
      | i + 1 =>
        simp
        rw [← ih (i := i) (j := j) (by nlinarith [j'.isLt]) (by grind) (by simp_all)]
        grind
    ·
      grind


-- created on 2025-11-09
