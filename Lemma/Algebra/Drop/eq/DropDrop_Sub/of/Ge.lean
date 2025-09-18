import Lemma.Algebra.DropDrop.eq.Drop_Add
import Lemma.Algebra.EqAddSub.of.Ge
open Algebra


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
