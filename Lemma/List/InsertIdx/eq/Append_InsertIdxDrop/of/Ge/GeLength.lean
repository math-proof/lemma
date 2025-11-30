import Lemma.List.EqAppendTake__Drop
import Lemma.List.EqInsertIdx.of.LtLength
import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Gt
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Nat.LtSubS.of.Lt.Le
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_j : s.length ≥ j)
  (h : i ≥ j)
  (x : α) :
-- imply
  s.insertIdx i x = s.take j ++ (s.drop j).insertIdx (i - j) x := by
-- proof
  if h_i : s.length ≥ i then
    if h_j : i = j then
      subst h_j
      simp
      conv_lhs =>
        rw [← EqAppendTake__Drop s i]
      rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength]
      <;> rw [LengthTake.eq.Min_Length]
      <;> rw [EqMin.of.Le h_i]
      simp
    else
      apply InsertIdx.eq.Append_InsertIdxDrop.of.Gt ∘ Gt.of.Ge.Ne h
      assumption
  else
    rw [EqInsertIdx.of.LtLength (by omega)]
    rw [EqInsertIdx.of.LtLength]
    ·
      simp
    ·
      simp at h_i
      simp
      apply LtSubS.of.Lt.Le h_j h_i


-- created on 2025-10-03
-- updated on 2025-11-27
