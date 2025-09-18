import Lemma.Basic


@[main]
private lemma main
  {a : List α}
  {b : List α}
-- given
  (h : HEq a b) :
-- imply
  a = b := by
-- proof
  simp_all


-- created on 2025-05-21
-- updated on 2025-05-22
