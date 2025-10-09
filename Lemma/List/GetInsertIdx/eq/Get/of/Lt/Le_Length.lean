import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.List.GetInsertIdx.eq.Get.of.Lt.Lt_Length
open List


@[main]
private lemma fin
  {v : List α}
-- given
  (h : i ≤ v.length)
  (h_ij : j < i)
  (a : α) :
-- imply
  have h_i : j < (v.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h]
    linarith
  (v.insertIdx i a).get ⟨j, h_i⟩ = v.get ⟨j, by linarith⟩ := by
-- proof
  apply GetInsertIdx.eq.Get.of.Lt.Lt_Length.fin
  assumption


@[main]
private lemma main
  {v : List α}
-- given
  (h : i ≤ v.length)
  (h_ij : j < i)
  (a : α) :
-- imply
  have : i < (v.insertIdx i a).length := by
    rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h]
    linarith
  (v.insertIdx i a)[j] = v[j] := by
-- proof
  apply fin h h_ij


-- created on 2025-10-09
