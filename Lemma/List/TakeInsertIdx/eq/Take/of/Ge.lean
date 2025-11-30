import Lemma.List.EqInsertIdx.of.LtLength
import Lemma.List.EqTakeAppend.of.Eq_Length
import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Ge.GeLength
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Le.of.Le.Le
open List Nat


@[main]
private lemma main
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
