import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Gt
import Lemma.List.EqAppendTake__Drop
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.Le_Length
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Nat.EqMin.of.Le
open Algebra List Nat


@[main]
private lemma main
  {a : List α}
-- given
  (h_i : i ≤ a.length)
  (h : i ≥ j)
  (x : α) :
-- imply
  a.insertIdx i x = a.take j ++ (a.drop j).insertIdx (i - j) x := by
-- proof
  by_cases h_j : i = j
  ·
    subst h_j
    simp
    conv_lhs =>
      rw [← EqAppendTake__Drop a i]
    rw [InsertIdxAppend.eq.Append_InsertIdx.of.Le_Length]
    <;> rw [LengthTake.eq.Min_Length]
    <;> rw [EqMin.of.Le h_i]
    simp
  ·
    apply InsertIdx.eq.Append_InsertIdxDrop.of.Gt ∘ Gt.of.Ge.Ne h
    assumption


-- created on 2025-10-03
