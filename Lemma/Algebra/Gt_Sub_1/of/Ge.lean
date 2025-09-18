import Lemma.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≥ y) :
-- imply
  x > y - 1 := by
-- proof
  linarith


-- created on 2025-03-28
