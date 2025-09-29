import sympy.Basic


@[main]
private lemma main
  {x : α}
  {A B : Set α}
-- given
  (h₀ : A ⊆ B)
  (h₁ : x ∈ A) :
-- imply
  x ∈ B :=
-- proof
  h₀ h₁


-- created on 2025-03-02
-- updated on 2025-07-19
