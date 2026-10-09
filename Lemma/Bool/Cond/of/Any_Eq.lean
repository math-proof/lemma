import sympy.Basic


@[path]
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


-- created on 2021-08-09
