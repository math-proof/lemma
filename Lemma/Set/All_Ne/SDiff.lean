import sympy.Basic


@[path]
private lemma main
  {y : α} :
-- imply
  ∀ x ∈ (Set.univ : Set α) \ {y}, x ≠ y := by
-- proof
  intro x hx
  simpa using hx.2


-- created on 2021-04-21
-- updated on 2026-10-17
