import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : (Fin n → ℂ) → ℤ}
-- given
  (h₀ : ∀ x ∈ {x | f x = 1}, g x = 1)
  (h₁ : ∀ x ∈ {x | g x = 1}, f x = 1) :
-- imply
  {x | f x = 1} = {x | g x = 1} := by
-- proof
  ext x
  exact ⟨fun hx => h₀ x hx, fun hx => h₁ x hx⟩


-- created on 2020-07-09
