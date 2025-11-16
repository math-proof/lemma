import Lemma.Int.SubSub
import Lemma.List.EqGetSSlicedIndices'.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt
import Lemma.List.EqLengthGetSlicedIndices'.of.LeSubAddMul.GtSubAddMul
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.SubAdd.eq.AddSub.of.Ge
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.Add
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.Gt_0
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.Ne_0
import Lemma.Rat.EqCeilDivSubMul.of.Lt
open Int List Nat Rat


@[main]
private lemma main
  {j' : Fin d}
-- given
  (h_stop : n * d + j > j + j')
  (h_start : n * d + j ≤ N)
  (h_i : i < n) :
-- imply
  have h_step := Gt_0 j'
  have := EqLengthGetSlicedIndices'.of.LeSubAddMul.GtSubAddMul h_stop h_start
  (Nat.sliced_indices' h_stop h_start h_step)[i]'(by simp [this]; omega) = (n - i) * d + j - 1 := by
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
        apply EqGetSSlicedIndices'.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt
        repeat grind
    ·
      have h := Ge.of.NotLt h_start?
      simp [MulAdd.eq.AddMulS, Add.comm] at h
      have h_j := j'.isLt
      have h_n : n = 0 := by
        by_contra h_n
        have h_n := Gt_0.of.Ne_0 h_n
        nlinarith
      subst h_n
      simp
      grind


-- created on 2025-11-09
