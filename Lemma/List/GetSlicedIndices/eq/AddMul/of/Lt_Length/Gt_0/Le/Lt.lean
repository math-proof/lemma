import Lemma.Int.EqToNatCeil
import Lemma.List.EqGetSSlicedIndices.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.CoeAdd_1.eq.AddCoe_1
import Lemma.Nat.Eq_0.of.LeAdd
import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.Lt_Add.of.Gt_0
open Nat List Int


@[main]
private lemma main
-- given
  (h_start : j < m * n)
  (h_stop : m * n ≤ m * n)
  (h_step : n > 0)
  (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step)[i] = i * n + j := by
-- proof
  induction n generalizing i j with
  | zero =>
    simp
    linarith
  | succ n ih =>
    unfold Nat.sliced_indices
    split_ifs with h_start?
    ·
      match i with
      | 0 =>
        simp
      | i + 1 =>
        simp
        sorry
    ·
      have h_length := LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step
      have h := Ge.of.NotLt h_start?
      rw [Add.comm] at h
      rw [AddAdd.eq.Add_Add] at h
      sorry


-- created on 2025-11-07
