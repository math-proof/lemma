import Lemma.List.ProdDrop.eq.Get.of.EqLength_Add_1
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  [MulOneClass α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  (s.drop (s.length - 1)).prod = s[s.length - 1] := by
-- proof
  apply ProdDrop.eq.Get.of.EqLength_Add_1 (n := s.length - 1)
  rw [EqAddSub.of.Ge (by omega)]


-- created on 2025-11-24
