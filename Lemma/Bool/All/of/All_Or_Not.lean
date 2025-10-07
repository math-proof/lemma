import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {A : Set α}
-- given
  (h : ∀ x, p x ∨ x ∉ A) :
-- imply
  ∀ x ∈ A, p x := by
-- proof
  -- Introduce the arbitrary element x and the assumption that x ∈ A
  intro x hx
  -- Consider the two cases from the disjunction in the hypothesis
  cases h x with
  | inl h_p =>
    -- Case 1: p x holds directly
    assumption
  | inr h_notin =>
    -- Case 2: x ∉ A, which contradicts the assumption x ∈ A
    contradiction


-- created on 2025-04-27
