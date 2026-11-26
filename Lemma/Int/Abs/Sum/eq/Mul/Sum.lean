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
  |y - (∑ i < n, x i) / n| = |∑ i < n, (y - x i)| / n := by
-- proof
  simp only [Nat.Iio_eq_range]
  have hn : (0 : ℝ) < n := by exact_mod_cast h₀
  have e : y - (Finset.range n).sum (fun i => x i) / n = (Finset.range n).sum (fun i => y - x i) / n := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [e, abs_div, abs_of_pos hn]


-- created on 2018-08-02
-- updated on 2026-11-26
