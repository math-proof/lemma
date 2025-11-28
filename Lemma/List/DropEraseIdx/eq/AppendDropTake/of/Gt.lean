import Lemma.List.DropEraseIdx.eq.AppendDropTake.of.Ge
import Lemma.Nat.Ge.of.Gt
open List Nat


@[main]
private lemma main
-- given
  (h : i > j)
  (s : List α) :
-- imply
  (s.eraseIdx i).drop j = (s.take i).drop j ++ s.drop (i + 1) := by
-- proof
  apply DropEraseIdx.eq.AppendDropTake.of.Ge
  apply Ge.of.Gt h


-- created on 2025-11-28
