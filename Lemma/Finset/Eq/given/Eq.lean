import Mathlib.Algebra.BigOperators.Intervals
import sympy.Basic


@[main]
private lemma rsolve
  {x f : ℕ → ℝ}
  {c : ℝ}
-- given
  (_h₀ : c ≠ 0)
  (h : ∀ n, x n = x 0 * c ^ n + ∑ k ∈ Finset.range n, f k * c ^ (n - k - 1)) :
-- imply
  ∀ n, x (n + 1) = c * x n + f n := by
-- proof
  have hstep : ∀ n, ∑ k ∈ Finset.range (n + 1), f k * c ^ (n + 1 - k - 1) = c * ∑ k ∈ Finset.range n, f k * c ^ (n - k - 1) + f n := by
    intro n
    rw [Finset.sum_range_succ, Finset.mul_sum, show n + 1 - n - 1 = 0 by omega, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show n + 1 - k - 1 = (n - k - 1) + 1 by omega, pow_succ]
    ring
  intro n
  rw [h (n + 1), h n, hstep]
  ring


-- created on 2026-09-27
