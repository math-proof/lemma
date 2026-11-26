import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : f (n + 1) = 0) :
-- imply
  ∑ k < (n + 1), f k * g k = -∑ k < (n + 1), (f (k + 1) - f k) * ∑ i < (k + 1), g i := by
-- proof
  have A : ∀ m, ∑ k < (m + 1), f k * g k =
      f m * ∑ i < (m + 1), g i - ∑ k < m, (f (k + 1) - f k) * ∑ i < (k + 1), g i := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.Iio_eq_range]
      simp
    | succ m ih =>
      simp only [Nat.Iio_eq_range] at ih ⊢
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (f (k + 1) - f k) * (Finset.range (k + 1)).sum g),
        Finset.sum_range_succ g (m + 1)]
      ring
  simp only [Nat.Iio_eq_range] at A ⊢
  rw [A n, Finset.sum_range_succ (fun k => (f (k + 1) - f k) * (Finset.range (k + 1)).sum g), h]
  ring


-- created on 2023-06-03
