import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Ge.Le_Length
open List


@[main]
private lemma fin
  {s : List α}
-- given
  (h : i ≤ s.length)
  (a : α) :
-- imply
  have h_i : i < (s.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h]
    linarith
  (s.insertIdx i a).get ⟨i, h_i⟩ = a := by
-- proof
  simp


@[main]
private lemma main
  {s : List α}
-- given
  (h : i ≤ s.length)
  (a : α) :
-- imply
  have : i < (s.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h]
    linarith
  (s.insertIdx i a)[i] = a := by
-- proof
  apply fin h


-- created on 2025-10-03
