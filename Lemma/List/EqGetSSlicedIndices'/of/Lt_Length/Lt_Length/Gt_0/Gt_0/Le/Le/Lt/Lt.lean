import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.Lt.of.Lt.Le
import Lemma.List.LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt
import Lemma.Algebra.LeSub.of.Le
import Lemma.Algebra.Lt_CeilDivSubSub.of.Add_1.lt.CeilDivSub.Gt
import Lemma.Algebra.Gt.of.GtSub
import Lemma.Rat.LeToNatCeil_1.of.Ge_Sub
open Algebra List Rat


@[main]
private lemma main
-- given
  (h_stop : start > stop)
  (h_stop' : start' > stop')
  (h_start : start ≤ n)
  (h_start' : start' ≤ n')
  (h_step : step > 0)
  (h_step' : step' > 0)
  (h_Eq_start : start' = start)
  (h_Eq_stop : stop' = stop)
  (h_Eq_step : step' = step)
  (h_i : i < (Nat.sliced_indices' h_stop h_start h_step).length)
  (h_i' : i < (Nat.sliced_indices' h_stop' h_start' h_step').length) :
-- imply
  (Nat.sliced_indices' h_stop h_start h_step)[i].val = (Nat.sliced_indices' h_stop' h_start' h_step')[i].val := by
-- proof
  induction i generalizing start start' with
  | zero =>
    -- Base case: The first elements of both slices are the same
    unfold Nat.sliced_indices'
    split_ifs <;> simp_all
  | succ i ih =>
    -- Inductive step: Use the inductive hypothesis to show the next elements are the same
    unfold Nat.sliced_indices'
    -- Split the cases based on whether the next index is within bounds
    split_ifs with h
    ·
      rw [LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt h_stop h_start h_step] at h_i
      have h_stop : start - step > stop := by
        linarith
      have h_start := LeSub.of.Le h_start step
      have h_gt := Gt.of.GtSub h_stop
      have h_i : i < (Nat.sliced_indices' h_stop h_start h_step).length := by
        rw [LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt h_stop h_start h_step]
        simp_all
        apply Lt_CeilDivSubSub.of.Add_1.lt.CeilDivSub.Gt h_gt
        assumption
      rw [LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt h_stop' h_start' h_step'] at h_i'
      have h_stop' : start' - step' > stop' := by
        simp_all
      have h_start' : start' - step' ≤ n' := LeSub.of.Le h_start' step'
      have h_i' : i < (Nat.sliced_indices' h_stop' h_start' h_step').length := by
        rw [LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt h_stop' h_start' h_step']
        simp_all
        apply Lt_CeilDivSubSub.of.Add_1.lt.CeilDivSub.Gt h_gt
        assumption
      simp [h_stop']
      apply ih (start := start - step) (start' := start' - step') h_stop h_stop' (by simp_all)
      rw [h_Eq_start, h_Eq_step]
    ·
      have h := Ge.of.NotLt h
      have h := LeToNatCeil_1.of.Ge_Sub h
      rw [← LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt h_stop h_start h_step] at h
      have := Lt.of.Lt.Le h_i h
      contradiction


-- created on 2025-05-28
