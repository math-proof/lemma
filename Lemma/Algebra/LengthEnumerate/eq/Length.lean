import stdlib.List
import Lemma.Basic


@[main]
private lemma main
-- given
  (a : List α) :
-- imply
  a.enumerate.length = a.length := by
-- proof
  simp [List.enumerate]


-- created on 2025-06-02
