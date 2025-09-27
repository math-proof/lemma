import stdlib.List
import Lemma.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : i > v.length)
  (a : α) :
-- imply
  (v.insertIdx i a).length = v.length := by
-- proof
  apply List.length_insertIdx_of_length_lt h


-- created on 2025-07-12
