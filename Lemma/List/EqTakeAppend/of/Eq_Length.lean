import stdlib.List
import Lemma.List.EqTakeAppend
open List


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length = n)
  (b : List α) :
-- imply
  (a ++ b).take n = a := by
-- proof
  rw [← h]
  apply EqTakeAppend


-- created on 2025-05-17
