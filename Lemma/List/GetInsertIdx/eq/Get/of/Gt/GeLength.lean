import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import Lemma.List.GetInsertIdx.eq.Get.of.Gt.GtLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i)
  (h_ij : i > j)
  (a : α) :
-- imply
  have : i < (s.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.GeLength h]
    linarith
  (s.insertIdx i a)[j] = s[j] := by
-- proof
  apply GetInsertIdx.eq.Get.of.Gt.GtLength _ h_ij


@[main]
private lemma fin
  {s : List α}
-- given
  (h : s.length ≥ i)
  (h_ij : i > j)
  (a : α) :
-- imply
  have h_i : j < (s.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.GeLength h]
    linarith
  (s.insertIdx i a).get ⟨j, h_i⟩ = s.get ⟨j, by linarith⟩ :=
-- proof
  main h h_ij a


-- created on 2025-10-09
