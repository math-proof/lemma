import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {h : ℕ → ℝ}
-- given
  (h₀ : ∀ k < n, h k ≤ 0) :
-- imply
  ∑ k < n, h k ≤ 0 := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  exact Finset.sum_nonpos (fun k hk => h₀ k (Finset.mem_range.mp hk))


-- created on 2019-12-06
