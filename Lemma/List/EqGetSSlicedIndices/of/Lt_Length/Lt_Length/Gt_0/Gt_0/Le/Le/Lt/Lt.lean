import stdlib.Slice
import Lemma.Nat.Ge.of.NotLt
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Rat.LeToNatCeil_1.of.Le_Add
import Lemma.Nat.Lt.of.Lt.Le
import Lemma.Algebra.Lt_CeilDivSub_Add.of.Add_1.lt.CeilDivSub
open Algebra List Rat Nat


@[main]
private lemma main
-- given
  (h_start : start < stop)
  (h_start' : start' < stop')
  (h_stop : stop ≤ n)
  (h_stop' : stop' ≤ n')
  (h_step : step > 0)
  (h_step' : step' > 0)
  (h_Eq_start : start' = start)
  (h_Eq_stop : stop' = stop)
  (h_Eq_step : step' = step)
  (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length)
  (h_i' : i < (Nat.sliced_indices h_start' h_stop' h_step').length) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step)[i].val = (Nat.sliced_indices h_start' h_stop' h_step')[i].val := by
-- proof
  induction i generalizing start start' with
  | zero =>
    -- Base case: The first elements of both slices are the same
    unfold Nat.sliced_indices
    split_ifs <;> simp_all
  | succ i ih =>
    -- Inductive step: Use the inductive hypothesis to show the next elements are the same
    unfold Nat.sliced_indices
    -- Split the cases based on whether the next index is within bounds
    split_ifs with h
    ·
      rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step] at h_i
      have h_start : start + step < stop := by
        linarith
      have h_i : i < (Nat.sliced_indices h_start h_stop h_step).length := by
        rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step]
        simp_all
        apply Lt_CeilDivSub_Add.of.Add_1.lt.CeilDivSub
        assumption
      rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start' h_stop' h_step'] at h_i'
      have h_start' : start' + step' < stop' := by
        linarith
      have h_i' : i < (Nat.sliced_indices h_start' h_stop' h_step').length := by
        rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start' h_stop' h_step']
        simp_all
        apply Lt_CeilDivSub_Add.of.Add_1.lt.CeilDivSub
        assumption
      simp [h_start']
      apply ih (start := start + step) (start' := start' + step') h_start h_start' (by simp_all) h_i h_i'
    ·
      have h := Ge.of.NotLt h
      have h := LeToNatCeil_1.of.Le_Add h
      rw [← LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step] at h
      have := Lt.of.Lt.Le h_i h
      contradiction


-- created on 2025-05-24
