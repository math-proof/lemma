import Lemma.List.EqAppendTake__Drop
open List


@[main]
private lemma main
-- given
  (s : List (List α))
  (n : ℕ) :
-- imply
  (s.take n).flatten ++ (s.drop n).flatten = s.flatten := by
-- proof
  rw [← EqAppendTake__Drop s n, List.flatten_append]
  simp


-- created on 2025-06-14
