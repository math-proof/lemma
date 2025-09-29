import sympy.Basic


@[main]
private lemma main
  {p q: Prop}
-- given
  (h : p → q):
-- imply
  p → p ∧ q :=
-- proof
  fun h_p =>
    ⟨h_p, h h_p⟩


-- created on 2025-01-12
