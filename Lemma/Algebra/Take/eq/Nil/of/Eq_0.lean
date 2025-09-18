import Lemma.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : i = 0) :
-- imply
  a.take i = .nil := by
-- proof
  simp_all


-- created on 2025-06-16
