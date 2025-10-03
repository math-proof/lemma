import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Ge.Le_Length
import Lemma.List.EqInsertIdx.of.Gt_Length
import Lemma.Algebra.EqTakeAppend.of.Eq_Length
import Lemma.Algebra.LengthTake.eq.Min_Length
import Lemma.Algebra.EqMin.of.Le
import Lemma.Algebra.Le.of.Le.Le
open List Algebra


@[main]
private lemma main
-- given
  (h : i ≥ j)
  (a : List α)
  (x : α) :
-- imply
  (a.insertIdx i x).take j = a.take j := by
-- proof
  by_cases h_i : i ≤ a.length
  ·
    rw [InsertIdx.eq.Append_InsertIdxDrop.of.Ge.Le_Length h_i h]
    apply EqTakeAppend.of.Eq_Length
    rw [LengthTake.eq.Min_Length]
    apply EqMin.of.Le ∘ Le.of.Le.Le h
    assumption
  ·
    rw [EqInsertIdx.of.Gt_Length]
    linarith


-- created on 2025-10-03
