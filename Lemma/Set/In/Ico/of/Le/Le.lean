import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : x ≤ b)
  (h₁ : a ≤ x) :
-- imply
  x ∈ Finset.Ico a (b + 1) := by
-- proof
  exact Finset.mem_Ico.mpr ⟨h₁, by omega⟩


-- created on 2021-05-23
