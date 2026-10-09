import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {y : ℝ}
-- given
  (h : ∀ i ∈ Finset.range n, x i ≠ y) :
-- imply
  y ∉ ⋃ i ∈ Finset.range n, ({x i} : Set ℝ) := by
-- proof
  simp only [Set.mem_iUnion, not_exists, Set.mem_singleton_iff]
  exact fun i hi e ↦ h i hi e.symm


-- created on 2021-01-14
