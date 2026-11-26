import Mathlib.Probability.Moments.Variance
import Initialize.Tactic.Attr.Basic
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
  (h₀ : ∀ i < n, π[x i] = μ)
  (h₁ : ∀ i < n, variance (x i) π = σ ^ 2)
  (h₂ : ∀ i < n, MemLp (x i) 2 π)
  (h₃ : 0 < n) :
-- imply
  ∫ ω, (∑ i < n, (x i ω - μ) ^ 2) / (n : ℝ) ∂π = σ ^ 2 := by
-- proof
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h₃.ne'
  rw [show (fun ω => (∑ i < n, (x i ω - μ) ^ 2) / (n : ℝ)) =
      fun ω => (n : ℝ)⁻¹ * ∑ i < n, (x i ω - μ) ^ 2 by
    ext ω
    ring]
  rw [integral_const_mul]
  have hsum : ∫ ω, ∑ i < n, (x i ω - μ) ^ 2 ∂π = ∑ i < n, σ ^ 2 := by
    rw [integral_finsetSum]
    ·
      refine sum_congr rfl fun i hi => ?_
      have hvar := variance_eq_integral (h₂ i (by simpa using hi)).aemeasurable
      rw [h₀ i (by simpa using hi)] at hvar
      rw [← hvar, h₁ i (by simpa using hi)]
    ·
      intro i hi
      apply ((h₂ i (by simpa using hi)).sub (memLp_const μ)).integrable_sq
  rw [hsum, sum_const, Nat.Iio_eq_range, card_range, nsmul_eq_mul]
  field_simp [hn]


-- created on 2023-11-18
-- updated on 2026-10-26
