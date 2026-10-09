import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : b ≥ x)
  (h₁ : x ≥ a) :
-- imply
  x ∈ Finset.Ico a (b + 1) := by
-- proof
  exact Finset.mem_Ico.mpr ⟨h₁, by omega⟩


-- created on 2021-04-07
