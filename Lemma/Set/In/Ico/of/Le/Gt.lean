import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : x ≤ b)
  (h₁ : x > a) :
-- imply
  x ∈ Finset.Ico (a + 1) (b + 1) := by
-- proof
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩


-- created on 2021-05-21
