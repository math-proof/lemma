import Lemma.List.DropTake.eq.ListGet.of.Lt_Length
open List


@[main]
private lemma main
  [MulOneClass α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  ((s.take (i + 1)).drop i).prod = s[i] := by
-- proof
  simp [DropTake.eq.ListGet.of.Lt_Length h]


-- created on 2025-10-27
