import sympy.sets.sets
import sympy.Basic


@[main]
private lemma rsolve
  {x : ℕ → ℝ}
  {c : ℝ}
  {h : ℕ → ℝ}
-- given
  (hr : ∀ n, x (n + 1) = x n * c + h n) :
-- imply
  ∀ n, x n = x 0 * c ^ n + ∑ k ∈ Finset.range n, h k * c ^ (n - k - 1) := by
-- proof
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [hr n, ih, Finset.sum_range_succ]
    have e : ∀ k ∈ Finset.range n, h k * c ^ (n - k - 1) * c = h k * c ^ (n + 1 - k - 1) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [mul_assoc, ← pow_succ, show n - k - 1 + 1 = n + 1 - k - 1 by omega]
    rw [add_mul, Finset.sum_mul, Finset.sum_congr rfl e, show n + 1 - n - 1 = 0 by omega, pow_zero, pow_succ]
    ring


-- created on 2026-09-27
