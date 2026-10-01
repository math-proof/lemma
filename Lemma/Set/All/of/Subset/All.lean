import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {A B : Set (Fin n → ℂ)}
  {f : (Fin n → ℂ) → ℂ}
-- given
  (h₀ : B ⊆ A)
  (h₁ : ∀ x ∈ A, f x = 1) :
-- imply
  ∀ x ∈ B, f x = 1 := by
-- proof
  exact fun x hx => h₁ x (h₀ hx)


-- created on 2020-04-01
