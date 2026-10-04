import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : p ∧ q → r) :
-- imply
  p ∧ q → q ∧ r :=
-- proof
  fun h_pq => ⟨h_pq.2, h h_pq⟩


-- created on 2019-10-08
