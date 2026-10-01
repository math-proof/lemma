import sympy.Basic


@[main]
private lemma main
-- given
  (h : p ↔ q) :
-- imply
  (p → q) ∧ (q → p) :=
-- proof
  ⟨h.mp, h.mpr⟩


-- created on 2026-09-27
