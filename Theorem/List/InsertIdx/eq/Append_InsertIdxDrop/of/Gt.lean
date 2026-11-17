module

public import Theorem.List.EqAppendTake__Drop
public import Theorem.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
public import Theorem.List.LengthTake.eq.Min_Length
public import Theorem.Nat.EqMin.of.Le
public import Theorem.List.EqInsertIdx.of.LtLength
public import Theorem.List.EqTake.of.LeLength
public import Theorem.List.Drop.eq.Nil.of.LeLength
public import Theorem.Nat.Ge.of.Gt
public import Theorem.Nat.Gt.of.Gt.Gt
public import Theorem.Nat.Ge_Min.of.Ge
public import Theorem.Nat.Sub.gt.Zero.is.Gt

public section

open List Nat


public theorem List.InsertIdx.eq.Append_InsertIdxDrop.of.Gt
  {s : List α}
-- given
  (h : i > j)
  (x : α) :
-- imply
  s.insertIdx i x = s.take j ++ (s.drop j).insertIdx (i - j) x := by
-- proof
  if h_j : j ≤ s.length then
    conv_lhs => rw [← EqAppendTake__Drop s j]
    rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength] <;>
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
    rw [EqTake.of.LeLength h_j]
    rw [Drop.eq.Nil.of.LeLength h_j]
    simp
    have h_ij := Sub.gt.Zero.of.Gt h
    rw [EqInsertIdx.of.LtLength h_ij]


-- created on 2025-10-03
