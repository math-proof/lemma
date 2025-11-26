import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.List.Drop.eq.Nil
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.drop (s.length - 1) = [s[s.length - 1]] := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by simp_all)]
  rw [EqAddSub.of.Ge (by linarith)]
  rw [Drop.eq.Nil]


-- created on 2025-06-17
