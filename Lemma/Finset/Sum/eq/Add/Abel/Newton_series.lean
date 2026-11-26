import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  (f g : ℕ → ℝ) :
-- imply
  ∑ k < (n + 1), f k * g k
    = f 0 * (∑ k < (n + 1), g k)
      + ∑ k < n, (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 1), g i := by
-- proof
  induction n with
  | zero =>
    simp only [Nat.Iio_eq_range]
    simp
  | succ n ih =>
    simp only [Nat.Iio_eq_range] at ih ⊢
    rw [Finset.sum_range_succ (fun k => f k * g k), ih]
    nth_rw 1 [Finset.sum_range_succ (fun k => g k) (n + 1)]
    have hsplit : ∀ k < n, ∑ i ∈ Finset.Ico (k + 1) (n + 2), g i =
      ∑ i ∈ Finset.Ico (k + 1) (n + 1), g i + g (n + 1) := by
      intro k hk
      have hlt : k + 1 ≤ n + 1 := by omega
      rw [Finset.sum_Ico_succ_top hlt]
    nth_rw 1 [Finset.sum_range_succ
      (fun k => (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 2), g i)]
    have hcong : ∑ k < n, (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 2), g i =
      ∑ k < n, (f (k + 1) - f k) * (∑ i ∈ Finset.Ico (k + 1) (n + 1), g i + g (n + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hsplit k (by simpa using hk)]
    simp only [Nat.Iio_eq_range] at hcong
    rw [hcong]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hmul : ∑ k < n, (f (k + 1) - f k) * g (n + 1) =
      (∑ k < n, (f (k + 1) - f k)) * g (n + 1) := by
      simp only [Nat.Iio_eq_range]
      simpa [mul_comm] using
        (Finset.sum_mul (Finset.range n) (fun k => f (k + 1) - f k) (g (n + 1))).symm
    simp only [Nat.Iio_eq_range] at hmul
    rw [hmul]
    have htele (m : ℕ) : ∑ k < m, (f (k + 1) - f k) = f m - f 0 := by
      induction m with
      | zero =>
        simp only [Nat.Iio_eq_range]
        simp
      | succ m ihm =>
        simp only [Nat.Iio_eq_range] at ihm ⊢
        rw [Finset.sum_range_succ, ihm]
        abel
    simp only [Nat.Iio_eq_range] at htele
    rw [htele n]
    have hlast : ∑ k ∈ Finset.Ico (n + 1) (n + 2), g k = g (n + 1) := by
      simp
    rw [hlast]
    ring


-- created on 2023-06-03
-- updated on 2026-10-26
