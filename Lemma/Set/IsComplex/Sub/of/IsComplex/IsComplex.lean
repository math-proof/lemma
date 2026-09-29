import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {a b : ℂ}
-- given
  (_h₀ : a ∈ (Set.univ : Set ℂ))
  (_h₁ : b ∈ (Set.univ : Set ℂ)) :
-- imply
  a - b ∈ (Set.univ : Set ℂ) :=
-- proof
  Set.mem_univ _


-- created on 2026-09-27
