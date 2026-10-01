import sympy.Basic


@[main]
private lemma main
  {b x a c d y : α}
-- given
  (h : b = x ∧ x = a ∧ c = a ∧ d = c ∧ b = y) :
-- imply
  d = y := by
-- proof
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  rw [h₄, h₃, ← h₂, ← h₁, h₅]


-- created on 2026-09-27
