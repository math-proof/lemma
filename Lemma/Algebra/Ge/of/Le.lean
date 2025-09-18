import Lemma.Basic


@[main]
private lemma main
  [LE α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  y ≥ x := by
-- proof
  exact h


-- created on 2024-07-01
