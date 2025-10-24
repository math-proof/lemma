import Lemma.List.DropTakePermute.eq.ListGet.of.GtLength_Add
open List


@[main]
private lemma main
  [MulOneClass α]
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : s.length > i + d) :
-- imply
  (((s.permute i d).take (i + d + 1)).drop (i + d)).prod = s[i] := by
-- proof
  simp [DropTakePermute.eq.ListGet.of.GtLength_Add h]


-- created on 2025-10-24
