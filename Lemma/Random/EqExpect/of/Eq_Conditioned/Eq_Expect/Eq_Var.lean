import Mathlib.Probability.Moments.Variance
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset


/--
Identical second moments: if every `x i` has mean `μ` and variance `σ²`, then
`E[∑_{i < n} (x i - μ)² / n] = σ²`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → ℝ}
  {μ σ : ℝ}
  {n : ℕ}
-- given
  (h₀ : ∀ i ∈ range n, π[x i] = μ)
  (h₁ : ∀ i ∈ range n, variance (x i) π = σ ^ 2)
  (h₂ : ∀ i ∈ range n, MemLp (x i) 2 π)
  (h₃ : 0 < n) :
-- imply
  ∫ ω, (∑ i ∈ range n, (x i ω - μ) ^ 2) / (n : ℝ) ∂π = σ ^ 2 := by
-- proof
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h₃.ne'
  rw [show (fun ω => (∑ i ∈ range n, (x i ω - μ) ^ 2) / (n : ℝ)) =
      fun ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, (x i ω - μ) ^ 2 by
    ext ω
    ring]
  rw [integral_const_mul]
  have hsum : ∫ ω, ∑ i ∈ range n, (x i ω - μ) ^ 2 ∂π = ∑ i ∈ range n, σ ^ 2 := by
    rw [integral_finsetSum]
    ·
      refine sum_congr rfl fun i hi => ?_
      have hvar := variance_eq_integral (h₂ i hi).aemeasurable
      rw [h₀ i hi] at hvar
      rw [← hvar, h₁ i hi]
    ·
      intro i hi
      apply ((h₂ i hi).sub (memLp_const μ)).integrable_sq
  rw [hsum, sum_const, card_range, nsmul_eq_mul]
  field_simp [hn]


-- created on 2026-10-11
-- updated on 2026-10-17
