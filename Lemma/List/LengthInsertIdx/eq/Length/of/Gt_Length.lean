import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : i > s.length)
  (a : α) :
-- imply
  (s.insertIdx i a).length = s.length := by
-- proof
  apply List.length_insertIdx_of_length_lt h


-- created on 2025-07-12
