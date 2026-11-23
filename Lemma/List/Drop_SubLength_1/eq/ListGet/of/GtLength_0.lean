import Theorem.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.List.Drop.eq.Nil
open List Nat


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.drop (s.length - 1) = [s[s.length - 1]] := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (Nat.sub_lt h (by decide))]
  rw [EqAddSub.of.Ge (by linarith)]
  rw [Drop.eq.Nil]


-- created on 2025-06-17
-- updated on 2026-11-22
