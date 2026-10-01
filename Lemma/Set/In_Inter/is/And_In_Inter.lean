import sympy.Basic


@[main]
private lemma main
  {x : α}
  {A B : Set α} :
-- imply
  x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ A ∩ B := by
-- proof
  constructor
  ·
    intro h
    exact ⟨h.1, h⟩
  ·
    intro h
    exact h.2


-- created on 2026-09-27
