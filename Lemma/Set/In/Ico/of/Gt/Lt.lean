import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : x > b)
  (h₁ : x < a) :
-- imply
  x ∈ Finset.Ico (b + 1) a := by
-- proof
  exact Finset.mem_Ico.mpr ⟨by omega, h₁⟩


-- created on 2021-04-20
