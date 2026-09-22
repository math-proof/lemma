import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : p ∧ r → q ∧ r) :
-- imply
  p ∧ r → q :=
-- proof
  fun h_pr => (h h_pr).left


-- created on 2019-10-08
-- updated on 2026-09-21
