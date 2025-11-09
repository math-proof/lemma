import Lemma.List.EqGetSSlicedIndices.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.List.EqLengthGetSlicedIndices.of.Gt_0.LeAddSMul.Lt_AddMul
import Lemma.Nat.Add
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.Lt_Add.of.Gt_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.Ne_0.of.Gt
open Nat List


@[main]
private lemma main
-- given
  (h_start : j < n * d + j)
  (h_stop : n * d + j ≤ n' * d + j)
  (h_step : d > 0)
  (h_i : i < n) :
-- imply
  have := List.EqLengthGetSlicedIndices.of.Gt_0.LeAddSMul.Lt_AddMul h_start h_stop h_step
  (Nat.sliced_indices h_start h_stop h_step)[i]'(by rwa [this]) = i * d + j := by
-- proof
  induction n generalizing i j with
  | zero =>
    simp
    linarith
  | succ n ih =>
    unfold Nat.sliced_indices
    have h_d := Ne_0.of.Gt h_step
    split_ifs with h_start?
    ·
      match i with
      | 0 =>
        simp
      | i + 1 =>
        simp [MulAdd.eq.AddMulS (a := i)]
        rw [AddAdd.comm]
        rw [AddAdd.eq.Add_Add]
        have h_start' : j + d < n * d + (j + d) := by
          apply Lt_Add.of.Gt_0
          linarith
        have h_stop' : n * d + (j + d) ≤ n' * d + (j + d) := by
          linarith [h_step]
        have h_length := LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step
        have h_i' : i < n := by simp_all
        have ih := ih h_start' h_stop' h_i'
        rw [← ih]
        have h_i? : i < (Nat.sliced_indices h_start? h_stop h_step).length := by
          rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt]
          rw [MulAdd.eq.AddMulS]
          rw [AddAdd.comm]
          rw [AddAdd.eq.Add_Add]
          simp_all
        apply EqGetSSlicedIndices.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt h_start? h_start' h_stop h_stop' h_step h_step rfl (by ring_nf) rfl h_i?
    ·
      have h_length := LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step
      have h := Ge.of.NotLt h_start?
      rw [Add.comm] at h
      rw [MulAdd.eq.AddMulS] at h
      simp [AddAdd.eq.Add_Add] at h
      simp [h_d] at h
      subst h
      simp at h_i
      simp_all


-- created on 2025-11-09
