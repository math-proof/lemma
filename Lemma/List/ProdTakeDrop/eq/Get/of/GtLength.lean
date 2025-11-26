import Lemma.List.TakeDrop.eq.ListGet.of.GtLength
open List


@[main]
private lemma main
  [MulOneClass α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  ((s.drop i).take 1).prod = s[i] := by
-- proof
  simp [TakeDrop.eq.ListGet.of.GtLength h]


-- created on 2025-10-25
