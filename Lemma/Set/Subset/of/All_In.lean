import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : ∀ x ∈ A, x ∈ B) :
-- imply
  A ⊆ B := by
-- proof
  assumption


-- created on 2025-07-20
