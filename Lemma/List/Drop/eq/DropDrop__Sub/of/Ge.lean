import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.Algebra.EqAdd_Sub.of.Ge
open Algebra List


@[main]
private lemma main
  {s : List α}
-- given
  (h : k ≥ i) :
-- imply
  s.drop k = (s.drop i).drop (k - i) := by
-- proof
  rw [DropDrop.eq.Drop_Add]
  rw [EqAdd_Sub.of.Ge h]


-- created on 2025-07-08
