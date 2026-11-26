import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Notation.Algebra.Power


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ} :
-- imply
  ∑ i < n, ∑ j < i, x i * x j = (∑ i < n, x i)² / 2 - (∑ i < n, x i ^ 2) / 2 := by
-- proof
  simp only [Nat.Iio_eq_range]
  have e : ((Finset.range n).sum (fun i => x i))² = 2 * (Finset.range n).sum (fun i => (Finset.range i).sum (fun j => x i * x j)) + (Finset.range n).sum (fun i => x i ^ 2) := by
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ x, Finset.sum_range_succ (fun i => (Finset.range i).sum (fun j => x i * x j)),
        Finset.sum_range_succ (fun i => x i ^ 2), add_sq, ih, ← Finset.mul_sum]
      ring
  rw [e]
  ring


-- created on 2019-11-12
-- updated on 2026-11-26
