import Lemma.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : y - 1 ≥ x) :
-- imply
  y > x := by
-- proof
  linarith


-- created on 2025-05-07
