import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℂ}
-- given
  (_h : ∀ i ∈ Finset.range n, x i ∈ (Set.univ : Set ℂ)) :
-- imply
  ∑ i ∈ Finset.range n, x i ∈ (Set.univ : Set ℂ) := by
-- proof
  exact Set.mem_univ _


-- created on 2026-09-27
