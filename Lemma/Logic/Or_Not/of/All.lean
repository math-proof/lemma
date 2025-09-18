import Lemma.Basic


@[main]
private lemma main
  {p : α → Prop}
  {A : Set α}

-- given
  (h : ∀ x ∈ A, p x) 
  (x : α):
-- imply
  p x ∨ x ∉ A := by
-- proof
  -- Use case analysis on whether x is in A or not
  by_cases hx : x ∈ A
  -- Case 1: x ∈ A
  -- From the hypothesis h, since x ∈ A, we have p x
  exact Or.inl (h x hx)
  -- Case 2: x ∉ A
  -- Directly use the fact that x ∉ A
  exact Or.inr hx


-- created on 2025-04-27
-- updated on 2025-07-29
