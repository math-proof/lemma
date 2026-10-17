import sympy.Basic


@[path]
private lemma main
  {y : α} :
-- imply
  ∀ x ∈ (Set.univ : Set α) \ {y}, x ≠ y := by
-- proof
  intro x hx
  simpa using hx.2


-- created on 2026-10-11
-- updated on 2026-10-17
