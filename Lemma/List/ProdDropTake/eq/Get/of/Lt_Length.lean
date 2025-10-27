import Lemma.List.DropTake.eq.ListGet.of.Lt_Length
open List


@[main]
private lemma main
  [MulOneClass α]
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  ((v.take (i + 1)).drop i).prod = v[i] := by
-- proof
  simp [DropTake.eq.ListGet.of.Lt_Length h]


-- created on 2025-10-27
