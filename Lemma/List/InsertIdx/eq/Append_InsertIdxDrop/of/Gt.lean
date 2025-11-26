import Lemma.List.EqAppendTake__Drop
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.GeLength
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Nat.EqMin.of.Le
import Lemma.List.EqInsertIdx.of.LtLength
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.Nat.Ge.of.Gt
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Nat.Ge_Min.of.Ge
import Lemma.Nat.Sub.gt.Zero.is.Gt
open List Nat


@[main]
private lemma main
  {a : List α}
-- given
  (h : i > j)
  (x : α) :
-- imply
  a.insertIdx i x = a.take j ++ (a.drop j).insertIdx (i - j) x := by
-- proof
  if h_j : j ≤ a.length then
    conv_lhs =>
      rw [← EqAppendTake__Drop a j]
    rw [InsertIdxAppend.eq.Append_InsertIdx.of.GeLength] <;>
      rw [LengthTake.eq.Min_Length]
    ·
      rwa [EqMin.of.Le]
    ·
      apply Ge_Min.of.Ge ∘ Ge.of.Gt
      assumption
  else
    simp at h_j
    have h_i := Gt.of.Gt.Gt h h_j
    rw [EqInsertIdx.of.LtLength h_i]
    have h_j := Ge.of.Gt h_j
    rw [EqTake.of.Ge_Length h_j]
    rw [Drop.eq.Nil.of.Ge_Length h_j]
    simp
    have h_ij := Sub.gt.Zero.of.Gt h
    rw [EqInsertIdx.of.LtLength h_ij]


-- created on 2025-10-03
