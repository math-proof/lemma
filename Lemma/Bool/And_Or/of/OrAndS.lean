import sympy.Basic


@[path]
private lemma main
  {p q r c : Prop}
-- given
  (h : p ∧ c ∨ q ∧ c ∨ r ∧ c) :
-- imply
  c ∧ (p ∨ q ∨ r) := by
-- proof
  grind


-- created on 2018-01-14
-- updated on 2023-05-20
