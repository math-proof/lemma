import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h : ∀ i < n, f i ≥ 0) :
-- imply
  ∑ i < n, f i ≥ 0 := by
-- proof
  try simp only [Nat.Iio_eq_range, ← Finset.mem_range] at *
  exact Finset.sum_nonneg h


-- created on 2019-01-18
