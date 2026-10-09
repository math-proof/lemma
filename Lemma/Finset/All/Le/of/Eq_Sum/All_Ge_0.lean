import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {a : ℝ}
-- given
  (h₀ : ∑ i ∈ Finset.range n, x i = a)
  (h₁ : ∀ i ∈ Finset.range n, x i ≥ 0) :
-- imply
  ∀ i ∈ Finset.range n, x i ≤ a := by
-- proof
  intro i hi
  rw [← h₀]
  exact Finset.single_le_sum h₁ hi


-- created on 2023-08-20
