import sympy.Basic


@[main]
private lemma main
  {x : α}
  {A B C : Set α}
-- given
  (h : x ∈ A ∨ x ∈ B ∨ x ∈ C) :
-- imply
  x ∈ A ∪ B ∪ C := by
-- proof
  rcases h with h | h | h
  ·
    exact Or.inl (Or.inl h)
  ·
    exact Or.inl (Or.inr h)
  ·
    exact Or.inr h


-- created on 2026-09-27
