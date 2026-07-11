import Lemma.List.DropCons_Append_List.eq.ListGet.of.GtLength_0
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > 0)
  (n a : α) :
-- imply
  ((n :: (s ++ [a])).drop s.length).prod = s[s.length - 1] * a := by
-- proof
  rw [DropCons_Append_List.eq.ListGet.of.GtLength_0 (by grind)]
  simp


-- created on 2026-07-11
