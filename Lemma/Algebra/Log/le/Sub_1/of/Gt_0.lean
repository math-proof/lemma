import Lemma.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  x.log ≤ x - 1 :=
-- proof
  Real.log_le_sub_one_of_pos h


-- created on 2025-07-01
