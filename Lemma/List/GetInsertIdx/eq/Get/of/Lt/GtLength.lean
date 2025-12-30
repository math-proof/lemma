import Lemma.List.GetInsertIdx.eq.Get.of.Lt.GeLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_j : s.length > j)
  (h_i : i < j)
  (a : α) :
-- imply
  (s.insertIdx i a)[j]'(by grind) = s[j - 1] := by
-- proof
  apply GetInsertIdx.eq.Get.of.Lt.GeLength (by grind) h_i


@[main]
private lemma fin
  {s : List α}
-- given
  (h_j : s.length > j)
  (h_i : i < j)
  (a : α) :
-- imply
  (s.insertIdx i a).get ⟨j, by grind⟩ = s.get ⟨j - 1, by grind⟩ :=
-- proof
  main h_j h_i a


-- created on 2025-11-17
