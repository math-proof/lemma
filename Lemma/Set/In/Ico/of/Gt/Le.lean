import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : b > x)
  (h₁ : a ≤ x) :
-- imply
  x ∈ Finset.Ico a b := by
-- proof
  exact Finset.mem_Ico.mpr ⟨h₁, h₀⟩


-- created on 2021-04-19
