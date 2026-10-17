import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  (f g : ℕ → ℝ) :
-- imply
  ∑ k ∈ Finset.range (n + 1), f k * g k
    = f 0 * ∑ k ∈ Finset.range (n + 1), g k
      + ∑ k ∈ Finset.range n, (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 1), g i := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun k => f k * g k), ih]
    nth_rw 1 [Finset.sum_range_succ (fun k => g k) (n + 1)]
    have hsplit : ∀ k ∈ Finset.range n, ∑ i ∈ Finset.Ico (k + 1) (n + 2), g i =
      ∑ i ∈ Finset.Ico (k + 1) (n + 1), g i + g (n + 1) := by
      intro k hk
      have hk : k < n := by simpa [Finset.mem_range] using hk
      have hlt : k + 1 ≤ n + 1 := by omega
      rw [Finset.sum_Ico_succ_top hlt]
    nth_rw 1 [Finset.sum_range_succ
      (fun k => (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 2), g i)]
    have hcong : ∑ k ∈ Finset.range n, (f (k + 1) - f k) * ∑ i ∈ Finset.Ico (k + 1) (n + 2), g i =
      ∑ k ∈ Finset.range n, (f (k + 1) - f k) * (∑ i ∈ Finset.Ico (k + 1) (n + 1), g i + g (n + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hsplit k hk]
    rw [hcong]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hmul : ∑ k ∈ Finset.range n, (f (k + 1) - f k) * g (n + 1) =
      (∑ k ∈ Finset.range n, (f (k + 1) - f k)) * g (n + 1) := by
      simpa [mul_comm] using
        (Finset.sum_mul (Finset.range n) (fun k => f (k + 1) - f k) (g (n + 1))).symm
    rw [hmul]
    have htele (m : ℕ) : ∑ k ∈ Finset.range m, (f (k + 1) - f k) = f m - f 0 := by
      induction m with
      | zero =>
        simp
      | succ m ihm =>
        rw [Finset.sum_range_succ, ihm]
        abel
    rw [htele n]
    have hlast : ∑ k ∈ Finset.Ico (n + 1) (n + 2), g k = g (n + 1) := by
      simp
    rw [hlast]
    ring


-- created on 2026-10-11
-- updated on 2026-10-17
