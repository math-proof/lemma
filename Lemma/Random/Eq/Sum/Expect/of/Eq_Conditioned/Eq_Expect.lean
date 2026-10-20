import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic
open MeasureTheory Finset


/--
Uncorrelated coordinates with common mean: `∑_{j < k < n} E[x j x k] = C(n, 2) μ²`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {x : ℕ → Ω → ℝ}
  {π : Measure Ω}
  {μ : ℝ}
  {n : ℕ}
-- given
  (h₀ : ∀ j k, j < k → ∫ ω, x j ω * x k ω ∂π = μ ^ 2) :
-- imply
  ∑ k ∈ range n, ∑ j ∈ range k, ∫ ω, x j ω * x k ω ∂π = (n.choose 2 : ℝ) * μ ^ 2 := by
-- proof
  have hsum : ∑ k ∈ range n, ∑ j ∈ range k, ∫ ω, x j ω * x k ω ∂π =
    ∑ k ∈ range n, ((k : ℕ) : ℝ) * μ ^ 2 := by
    refine sum_congr rfl fun k _ => ?_
    rw [sum_congr rfl fun j hj => h₀ j k (mem_range.1 hj), sum_const, card_range, nsmul_eq_mul]
  rw [hsum]
  have hid : ∑ k ∈ range n, (k : ℝ) = (n.choose 2 : ℝ) := by
    rw [← Nat.cast_sum, sum_range_id, Nat.choose_two_right]
  calc
    _ = ∑ k ∈ range n, μ ^ 2 * k := by
      refine sum_congr rfl fun _ _ => mul_comm _ _
    _ = μ ^ 2 * ∑ k ∈ range n, (k : ℝ) := by rw [← mul_sum]
    _ = μ ^ 2 * (n.choose 2 : ℝ) := by rw [hid]
    _ = (n.choose 2 : ℝ) * μ ^ 2 := mul_comm _ _


-- created on 2023-10-12
-- updated on 2026-10-17
