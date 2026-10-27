import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℂ}
-- given
  (_h : ∀ i ∈ Finset.range n, x i ∈ (Set.univ : Set ℂ)) :
-- imply
  ∑ i ∈ Finset.range n, x i ∈ (Set.univ : Set ℂ) := by
-- proof
  exact Set.mem_univ _


-- created on 2023-05-03
