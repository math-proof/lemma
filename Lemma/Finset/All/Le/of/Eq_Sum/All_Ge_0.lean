import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {a : ℝ}
-- given
  (h₀ : ∑ i < n, x i = a)
  (h₁ : ∀ i < n, x i ≥ 0) :
-- imply
  ∀ i < n, x i ≤ a := by
-- proof
  try simp only [Nat.Iio_eq_range, ← Finset.mem_range] at *
  intro i hi
  rw [← h₀]
  exact Finset.single_le_sum h₁ hi


-- created on 2023-08-20
