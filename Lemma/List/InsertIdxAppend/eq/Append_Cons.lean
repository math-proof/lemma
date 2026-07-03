import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
open List


@[main]
private lemma main
-- given
  (a b : List α)
  (x : α) :
-- imply
  (a ++ b).insertIdx a.length x = a ++ x :: b := by
-- proof
  have := InsertIdxAppend.eq.Append_InsertIdx a b 0 x
  grind


-- created on 2026-07-03
