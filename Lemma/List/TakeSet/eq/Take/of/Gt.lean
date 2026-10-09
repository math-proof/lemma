import Lemma.List.TakeSet.eq.Take.of.Ge
import Lemma.Nat.Ge.of.Gt
open List Nat


@[path]
private lemma main
  {s : List α}
-- given
  (h : i > j)
  (a : α) :
-- imply
  (s.set i a).take j = s.take j := by
-- proof
  apply TakeSet.eq.Take.of.Ge
  apply Ge.of.Gt h


-- created on 2025-11-29
