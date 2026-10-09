import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {a b : ℂ}
-- given
  (_h₀ : a ∈ Complex.ofReal '' Set.Ioi 0)
  (_h₁ : b ∈ (Set.univ : Set ℂ)) :
-- imply
  b / a ∈ (Set.univ : Set ℂ) := by
-- proof
  exact Set.mem_univ _


-- created on 2023-05-03
