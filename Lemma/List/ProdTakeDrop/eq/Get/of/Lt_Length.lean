import Lemma.List.TakeDrop.eq.ListGet.of.Lt_Length
open List


@[main]
private lemma main
  [MulOneClass α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  ((s.drop i).take 1).prod = s[i] := by
-- proof
  simp [TakeDrop.eq.ListGet.of.Lt_Length h]


-- created on 2025-10-25
