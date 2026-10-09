import sympy.sets.sets
import sympy.Basic


@[path]
private lemma squeeze
  {A B : Set ℂ}
-- given
  (h₀ : A ⊆ B)
  (h₁ : B ⊆ A) :
-- imply
  A = B := by
-- proof
  exact Set.Subset.antisymm h₀ h₁


-- created on 2020-09-06
