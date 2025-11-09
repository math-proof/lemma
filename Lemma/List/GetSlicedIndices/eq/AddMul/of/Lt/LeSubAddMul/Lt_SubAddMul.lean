import Lemma.Int.SubSub
import Lemma.List.EqGetSSlicedIndices.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt
import Lemma.List.EqLengthGetSlicedIndices.of.LeSubAddMul.Lt_SubAddMul
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.Add
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.LtVal
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.Gt_0
import Lemma.Nat.Ne_0.of.Gt
import Lemma.Nat.Ne_0
import Lemma.Rat.EqCeilDivSubMul.of.Lt
open List Nat Int Rat


@[main]
private lemma main
  {j' : Fin d}
-- given
  (h_start : j < n * d + j - j')
  (h_stop : n * d + j - j' ≤ N)
  (h_i : i < n) :
-- imply
  have h_step := Gt_0 j'
  have := EqLengthGetSlicedIndices.of.LeSubAddMul.Lt_SubAddMul h_start h_stop
  (Nat.sliced_indices h_start h_stop h_step)[i]'(by rwa [this]) = i * d + j := by
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
        rw [AddAdd.comm, AddAdd.eq.Add_Add]
        rw [← ih (i := i) (j := j + d) (by grind) (by grind) (by simp_all)]
        apply EqGetSSlicedIndices.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt
        repeat grind
    ·
      have h := Ge.of.NotLt h_start?
      simp [Add.comm, MulAdd.eq.AddMulS] at h
      have h_j := LtVal j'
      have h_n : n = 0 := by
        by_contra h_n
        have h_n := Gt_0.of.Ne_0 h_n
        nlinarith
      grind


-- created on 2025-11-09
