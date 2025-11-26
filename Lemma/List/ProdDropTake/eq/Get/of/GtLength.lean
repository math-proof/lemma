import Lemma.List.DropTake.eq.ListGet.of.GtLength
open List


@[main]
private lemma main
  [MulOneClass α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  ((s.take (i + 1)).drop i).prod = s[i] := by
-- proof
  simp [DropTake.eq.ListGet.of.GtLength h]


-- created on 2025-10-27
