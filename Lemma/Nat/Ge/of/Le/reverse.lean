import sympy.Basic


@[main]
private lemma main
  [LE α]
  {x a : α}
-- given
  (h : x ≤ a) :
-- imply
  a ≥ x := by
-- proof
  exact h


-- created on 2019-05-23
