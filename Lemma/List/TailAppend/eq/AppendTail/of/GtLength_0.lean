import Lemma.List.TailAppend.eq.AppendTail.of.Ne_Nil
open List


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length > 0)
  (b : List α) :
-- imply
  (a ++ b).tail = a.tail ++ b := by
-- proof
  apply TailAppend.eq.AppendTail.of.Ne_Nil
  grind


-- created on 2025-07-06
-- updated on 2026-01-12
