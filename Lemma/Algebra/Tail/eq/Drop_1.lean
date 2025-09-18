import Lemma.Basic


@[main, comm]
private lemma main
  (s : List α) :
-- imply
  s.tail = s.drop 1 := by
-- proof
  simp


-- created on 2025-05-05
