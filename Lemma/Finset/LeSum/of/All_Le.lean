import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : ∀ i < n, f i ≤ g i) :
-- imply
  ∑ i < n, f i ≤ ∑ i < n, g i := by
-- proof
  try simp only [Nat.Iio_eq_range, ← Finset.mem_range] at *
  exact Finset.sum_le_sum h


-- created on 2019-01-26
