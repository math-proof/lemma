import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : p ∨ q → r) :
-- imply
  (p → r) ∧ (q → r) := by
-- proof
  exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩


-- created on 2026-10-03
