import Lemma.Int.GeAbs.is.Or


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : |x| ≥ a) :
-- imply
  x ≤ -a ∨ x ≥ a := by
-- proof
  exact Int.GeAbs.is.Or.mp h


-- created on 2018-07-28
