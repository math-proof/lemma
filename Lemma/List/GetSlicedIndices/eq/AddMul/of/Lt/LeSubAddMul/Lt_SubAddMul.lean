import Lemma.List.EqLengthGetSlicedIndices.of.LeSubAddMul.Lt_SubAddMul
import Lemma.Nat.AddAdd.eq.Add_Add
open List Nat


@[main]
private lemma main
  {j' : Fin d}
-- given
  (h_start : j < n * d + j - j')
  (h_stop : n * d + j - j' ≤ N)
  (h_i : i < n) :
-- imply
  (Nat.sliced_indices h_start h_stop (Gt_0 j'))[i]'(by rwa [EqLengthGetSlicedIndices.of.LeSubAddMul.Lt_SubAddMul h_start h_stop]) = i * d + j := by
-- proof
  induction n generalizing i j with
  | zero =>
    grind
  | succ n ih =>
    unfold Nat.sliced_indices
    split_ifs with h_start?
    ·
      match i with
      | 0 =>
        simp
      | i + 1 =>
        simp [MulAdd.eq.AddMulS (a := i)]
        rw [AddAdd.eq.Add_Add.comm]
        rw [← ih (i := i) (j := j + d) (by grind) (by grind) (by simp_all)]
        grind
    ·
      grind


-- created on 2025-11-09
