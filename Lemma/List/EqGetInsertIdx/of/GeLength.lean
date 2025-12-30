import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Ge.GeLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i)
  (a : α) :
-- imply
  have : i < (s.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.GeLength h]
    linarith
  (s.insertIdx i a)[i] = a := by
-- proof
  simp


@[main]
private lemma fin
  {s : List α}
-- given
  (h : s.length ≥ i)
  (a : α) :
-- imply
  have h_i : i < (s.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.GeLength h]
    linarith
  (s.insertIdx i a).get ⟨i, h_i⟩ = a :=
-- proof
  main h a


-- created on 2025-10-03
