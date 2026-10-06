import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : x ≥ b)
  (h₁ : x < a) :
-- imply
  x ∈ Finset.Ico b a := by
-- proof
  exact Finset.mem_Ico.mpr ⟨h₀, h₁⟩


-- created on 2021-04-10
-- updated on 2023-11-13
