module

public import Theorem.List.EqTakeAppend.of.Eq_Length
public import Theorem.List.InsertIdx.eq.Append_InsertIdxDrop.of.Ge.GeLength
public import Theorem.Nat.Le.of.Le.Le

public section

open List Nat


public theorem List.TakeInsertIdx.eq.Take.of.Ge
-- given
  (h : i ≥ j)
  (s : List α)
  (x : α) :
-- imply
  (s.insertIdx i x).take j = s.take j := by
-- proof
  if h_i : i ≤ s.length then
    rw [InsertIdx.eq.Append_InsertIdxDrop.of.Ge.GeLength (by omega) h]
    apply EqTakeAppend.of.Eq_Length
    rw [LengthTake.eq.Min_Length]
    apply EqMin.of.Le ∘ Le.of.Le.Le h
    assumption
  else
    rw [EqInsertIdx.of.LtLength]
    linarith


-- created on 2025-10-03
-- updated on 2025-11-27
