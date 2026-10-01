import sympy.Basic


@[main]
private lemma main
-- given
  (h : p ↔ q) :
-- imply
  (p → q) ∧ (q → p) :=
-- proof
  ⟨h.mp, h.mpr⟩


-- created on 2022-01-27
