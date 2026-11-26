import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Notation.Algebra.Power


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ} :
-- imply
  ∑ i < n, ∑ j < i, (x i - x j)² = n * ∑ i < n, x i ^ 2 - (∑ i < n, x i)² := by
-- proof
  simp only [Nat.Iio_eq_range]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have e : (Finset.range n).sum (fun j => (x n - x j)²) =
        n * x n ^ 2 - 2 * x n * (Finset.range n).sum x + (Finset.range n).sum (fun j => x j ^ 2) := by
      have : ∀ j ∈ Finset.range n, (x n - x j)² = x n ^ 2 - 2 * x n * x j + x j ^ 2 := fun j _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_range_succ (fun i => (Finset.range i).sum (fun j => (x i - x j)²)), ih, e, Finset.sum_range_succ (fun i => x i ^ 2),
      Finset.sum_range_succ x]
    push_cast
    ring


-- created on 2019-11-12
-- updated on 2026-11-26
