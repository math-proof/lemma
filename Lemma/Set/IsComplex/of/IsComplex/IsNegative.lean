import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {a b : ℂ}
-- given
  (_h₀ : b ∈ (Set.univ : Set ℂ))
  (_h₁ : a ∈ Complex.ofReal '' Set.Iio 0) :
-- imply
  b / a ∈ (Set.univ : Set ℂ) := by
-- proof
  exact Set.mem_univ _


-- created on 2023-05-03
