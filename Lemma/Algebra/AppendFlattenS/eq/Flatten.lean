import Lemma.List.EqAppendTake__Drop
open List


@[main]
private lemma main
-- given
  (v : List (List α))
  (n : ℕ) :
-- imply
  (v.take n).flatten ++ (v.drop n).flatten = v.flatten := by
-- proof
  rw [← EqAppendTake__Drop v n, List.flatten_append]
  simp


-- created on 2025-06-14
