import Lemma.List.TakeDrop.eq.ListGet.of.Lt_Length
open List


@[main]
private lemma main
  [MulOneClass α]
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  ((v.drop i).take 1).prod = v[i] := by
-- proof
  simp [TakeDrop.eq.ListGet.of.Lt_Length h]


-- created on 2025-10-25
