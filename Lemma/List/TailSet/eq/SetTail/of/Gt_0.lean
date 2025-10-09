import Lemma.Nat.EqAddSub.of.Ge
open Nat


@[main, comm]
private lemma main
-- given
  (h : i > 0)
  (s : List α)
  (a : α) :
-- imply
  (s.set i a).tail = s.tail.set (i - 1) a := by
-- proof
  simp
  rwa [EqAddSub.of.Ge]


-- created on 2025-07-05
