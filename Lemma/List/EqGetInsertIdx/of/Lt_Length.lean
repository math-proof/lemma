import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Ge.Le_Length
open List


@[main]
private lemma fin
  {v : List α}
-- given
  (h : i ≤ v.length)
  (a : α) :
-- imply
  have h_i : i < (v.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h]
    linarith
  (v.insertIdx i a).get ⟨i, h_i⟩ = a := by
-- proof
  simp


@[main]
private lemma main
  {v : List α}
-- given
  (h : i ≤ v.length)
  (a : α) :
-- imply
  have : i < (v.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h]
    linarith
  (v.insertIdx i a)[i] = a := by
-- proof
  apply fin h


-- created on 2025-10-03
