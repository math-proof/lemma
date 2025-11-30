import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
import Lemma.Nat.Ge.of.Gt
open List Nat


@[main]
private lemma main
-- given
  (h : i > j)
  (s : List α) :
-- imply
  (s.eraseIdx i).take j = s.take j := by
-- proof
  apply TakeEraseIdx.eq.Take.of.Ge
  apply Ge.of.Gt h


-- created on 2025-11-28
