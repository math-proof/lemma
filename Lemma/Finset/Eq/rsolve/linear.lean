import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (c : ℝ)
  (x h : ℕ → ℝ)
  {n : ℕ}
-- given
  (h₀ : ∀ n, x (n + 1) = x n * c + h n) :
-- imply
  x n = x 0 * c ^ n + ∑ k ∈ Finset.range n, h k * c ^ (n - k - 1) := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [h₀ n, ih, add_mul, Finset.sum_mul]
    have hpow : ∀ k ∈ Finset.range n, h k * c ^ (n - k - 1) * c = h k * c ^ (n + 1 - k - 1) := by
      intro k hk
      have hk : k < n := by simpa [Finset.mem_range] using hk
      have hsub : n - k - 1 + 1 = n + 1 - k - 1 := by
        have : k + 1 ≤ n := hk
        omega
      rw [mul_assoc, ← pow_succ, hsub]
    have hsum : ∑ k ∈ Finset.range n, h k * c ^ (n - k - 1) * c =
      ∑ k ∈ Finset.range n, h k * c ^ (n + 1 - k - 1) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact hpow k hk
    rw [hsum]
    have hhead : x 0 * c ^ n * c = x 0 * c ^ (n + 1) := by
      ring
    have htail : h n * c ^ (n + 1 - n - 1) = h n := by
      have : n + 1 - n - 1 = 0 := by omega
      simp
    rw [hhead, ← htail, add_assoc, ← Finset.sum_range_succ]


-- created on 2020-10-07
-- updated on 2026-10-26
