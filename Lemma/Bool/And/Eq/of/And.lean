import sympy.Basic


@[main]
private lemma just_intonation
  {a b c : α}
-- given
  (h : a = b ∧ b = c) :
-- imply
  a = c ∧ b = c := by
-- proof
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨h₁.trans h₂, h₂⟩


-- created on 2026-09-27
