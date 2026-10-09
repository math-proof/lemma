import sympy.Basic


@[path]
private lemma main
  {e : α}
  {A B : Set α}
-- given
  (h₀ : e ∈ A)
  (h₁ : e ∈ B) :
-- imply
  e ∈ A ∩ B := by
-- proof
  exact ⟨h₀, h₁⟩


-- created on 2023-08-26
