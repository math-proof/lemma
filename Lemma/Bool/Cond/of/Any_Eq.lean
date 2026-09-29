import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {y : α}
-- given
  (h : ∃ x ∈ S, x = y) :
-- imply
  y ∈ S := by
-- proof
  obtain ⟨x, hx, rfl⟩ := h
  exact hx


-- created on 2026-09-27
