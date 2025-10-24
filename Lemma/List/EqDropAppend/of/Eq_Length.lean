import stdlib.List
import Lemma.List.EqDropAppend
open List


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length = n)
  (b : List α) :
-- imply
  (a ++ b).drop n = b := by
-- proof
  rw [← h]
  apply EqDropAppend


-- created on 2025-05-17
