import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : b > x)
  (h₁ : x > a) :
-- imply
  x ∈ Finset.Ico (a + 1) b := by
-- proof
  exact Finset.mem_Ico.mpr ⟨by omega, h₀⟩


-- created on 2021-04-16
