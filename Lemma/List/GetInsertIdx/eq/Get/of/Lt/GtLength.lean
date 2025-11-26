import Lemma.List.GetInsertIdx.eq.Get.of.Lt.GeLength
open List


@[main]
private lemma fin
  {s : List α}
-- given
  (h_j : j < s.length)
  (h_i : i < j)
  (a : α) :
-- imply
  (s.insertIdx i a).get ⟨j, by grind⟩ = s.get ⟨j - 1, by grind⟩ := by
-- proof
  apply GetInsertIdx.eq.Get.of.Lt.GeLength.fin (by grind) h_i


@[main]
private lemma main
  {s : List α}
-- given
  (h_j : j < s.length)
  (h_i : i < j)
  (a : α) :
-- imply
  (s.insertIdx i a)[j]'(by grind) = s[j - 1] := by
-- proof
  apply fin h_j h_i


-- created on 2025-11-17
