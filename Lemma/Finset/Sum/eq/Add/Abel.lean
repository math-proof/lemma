import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ} :
-- imply
  ∑ k < (n + 1), f k * g k =
    f 0 * ∑ k < (n + 1), g k + ∑ k < n, (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 1), g i := by
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
  have e : ∀ k < n, (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 1), g i =
      (f (k + 1) - f k) * ∑ i < (n + 1), g i - (f (k + 1) - f k) * ∑ i < (k + 1), g i := by
    intro k hk
    simp only [Nat.Iio_eq_range]
    rw [Finset.sum_Ico_eq_sub _ (by omega)]
    ring
  rw [Finset.sum_congr rfl (fun x hx => e x (by simpa using hx)), Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [show ∑ i < n, (f (i + 1) - f i) = (Finset.range n).sum (fun i => f (i + 1) - f i) by
    simp only [Nat.Iio_eq_range]]
  rw [Finset.sum_range_sub, A n]
  ring


-- created on 2023-06-02
