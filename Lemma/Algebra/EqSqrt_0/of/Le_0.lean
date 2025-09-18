import Lemma.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ≤ 0) :
-- imply
  √x = 0 :=
-- proof
  Real.sqrt_eq_zero_of_nonpos h


-- created on 2025-04-06
