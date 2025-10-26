import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.Lt_Add.of.Gt_0
import Lemma.Nat.CoeAdd_1.eq.AddCoe_1
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.EqToNatCeil
import Lemma.List.EqGetSSlicedIndices.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt
import Lemma.Nat.Eq_0.of.LeAdd
open List Int Nat


@[main]
private lemma main
-- given
  (h_start : j < n + j)
  (h_stop : n + j ≤ n' + j)
  (h_step : 1 > 0)
  (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step)[i] = i + j := by
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
      | .zero =>
        simp
      | .succ i =>
        simp
        rw [AddAdd.eq.Add_Add (a := i)]
        rw [Add.comm (a := 1)]
        simp at h_i
        have h_start' : j + 1 < n + (j + 1) := by
          apply Lt_Add.of.Gt_0
          linarith
        have h_stop' : n + (j + 1) ≤ n' + (j + 1) := by
          omega
        have h_length := LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step
        have h_i' : i < (Nat.sliced_indices h_start' h_stop' h_step).length := by
          rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start' h_stop' h_step]
          simp_all
        have ih := ih h_start' h_stop' h_i'
        have h_nj : n + 1 + j = n + (j + 1) := by
          rw [AddAdd.eq.Add_Add]
          rw [Add.comm (a := 1)]
        rw [← ih]
        have h_i? : i < (Nat.sliced_indices h_start? h_stop h_step).length := by
          rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start? h_stop h_step]
          simp_all
          rw [AddCoe_1.eq.CoeAdd_1] at h_i
          rw [AddCoeS.eq.CoeAdd] at h_i
          rw [EqToNatCeil] at h_i
          ring_nf at h_i
          simp at h_i
          assumption
        apply EqGetSSlicedIndices.of.Lt_Length.Lt_Length.Gt_0.Gt_0.Le.Le.Lt.Lt h_start? h_start' h_stop h_stop' h_step h_step rfl (by ring_nf) rfl h_i? h_i'
    ·
      have h_length := LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step
      have h := Ge.of.NotLt h_start?
      rw [Add.comm] at h
      rw [AddAdd.eq.Add_Add] at h
      have h := Eq_0.of.LeAdd h
      subst h
      simp_all
      linarith


-- created on 2025-05-24
