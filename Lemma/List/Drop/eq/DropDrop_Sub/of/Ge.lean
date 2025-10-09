import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : k ≥ j) :
-- imply
  s.drop k = (s.drop (k - j)).drop j := by
-- proof
  rw [DropDrop.eq.Drop_Add]
  rw [EqAddSub.of.Ge h]


-- created on 2025-07-08
