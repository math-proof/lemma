import Lemma.Algebra.EqAppendTake__Drop
import Lemma.Algebra.InsertIdxAppend.eq.Append_InsertIdx.of.Le_Length
import Lemma.Algebra.LengthTake.eq.Min_Length
import Lemma.Algebra.EqMin.of.Le
import Lemma.List.EqInsertIdx.of.Gt_Length
import Lemma.Algebra.EqTake.of.Ge_Length
import Lemma.Algebra.Drop.eq.Nil.of.Ge_Length
import Lemma.Algebra.Ge.of.Gt
import Lemma.Algebra.Gt.of.Gt.Gt
import Lemma.Algebra.Ge_Min.of.Ge
open Algebra List


@[main]
private lemma main
  {a : List α}
-- given
  (h : i > j)
  (x : α) :
-- imply
  a.insertIdx i x = a.take j ++ (a.drop j).insertIdx (i - j) x := by
-- proof
  by_cases h_j : j ≤ a.length
  · 
    conv_lhs =>
      rw [← EqAppendTake__Drop a j]
    rw [InsertIdxAppend.eq.Append_InsertIdx.of.Le_Length] <;> 
      rw [LengthTake.eq.Min_Length]
    · 
      rwa [EqMin.of.Le]
    · 
      apply Ge_Min.of.Ge ∘ Ge.of.Gt
      assumption
  · 
    simp at h_j
    have h_i := Gt.of.Gt.Gt h h_j
    rw [EqInsertIdx.of.Gt_Length h_i]
    have h_j := Ge.of.Gt h_j
    rw [EqTake.of.Ge_Length h_j]
    rw [Drop.eq.Nil.of.Ge_Length h_j]
    simp
    have h_ij := Sub.gt.Zero.of.Gt.nat h
    rw [EqInsertIdx.of.Gt_Length h_ij]


-- created on 2025-10-03
