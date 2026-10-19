import Lemma.Nat.Eq.of.And.squeeze


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x = y) :
-- imply
  x ≤ y ∧ x ≥ y := by
-- proof
  exact Nat.Eq.of.And.squeeze h


-- created on 2019-04-05
