import sympy.Basic


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


-- created on 2019-05-24
