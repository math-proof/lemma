import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {y : ℝ}
-- given
  (h₀ : n > 0) :
-- imply
  (y - (∑ i < n, x i) / n) ^ 2 = (∑ i < n, (y - x i)) ^ 2 / n ^ 2 := by
-- proof
  have hn : (0 : ℝ) < n := by exact_mod_cast h₀
  have e : y - (∑ i < n, x i) / n = (∑ i < n, (y - x i)) / n := by
    try simp only [Nat.Iio_eq_range] at *
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [e, div_pow]


-- created on 2019-11-02
