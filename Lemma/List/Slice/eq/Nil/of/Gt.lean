import stdlib.List
import Lemma.List.Slice.eq.Nil.of.Ge
import Lemma.Nat.Ge.of.Gt
open List Nat


@[main]
private lemma main
  {a : List α}
-- given
  (h : start > stop) :
-- imply
  a.slice start stop = .nil := by
-- proof
  apply Slice.eq.Nil.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-07
