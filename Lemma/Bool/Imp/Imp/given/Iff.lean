import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p ↔ q) :
-- imply
  (p → q) ∧ (q → p) := by
-- proof
  exact ⟨h.mp, h.mpr⟩


-- created on 2022-01-27
