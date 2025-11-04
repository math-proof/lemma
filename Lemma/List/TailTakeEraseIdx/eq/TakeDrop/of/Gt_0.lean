import Lemma.List.TailTakeEraseIdx.eq.TakeDrop
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (s : List α)
  (h : i > 0) :
-- imply
  ((s.eraseIdx 1).take i).tail = (s.drop 2).take (i - 1) := by
-- proof
  rw [← TailTakeEraseIdx.eq.TakeDrop]
  rw [EqAddSub.of.Ge (by omega)]


-- created on 2025-11-04
