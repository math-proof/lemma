import Mathlib.Probability.Moments.Variance
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Control variate at the constant baseline `1`, with `E[f] = 0` and `b ∈ (0, 2)`:
the shifted product keeps the same mean and strictly smaller variance whenever `Var[f] ≠ 0`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {f : Ω → ℝ}
  {b : ℝ}
-- given
  (h₀ : π[f] = 0)
  (h₁ : 0 < b)
  (h₂ : b < 2)
  (h₃ : variance f π ≠ 0)
  (_ : MemLp f 2 π) :
-- imply
  π[fun ω => f ω * (1 - b)] = π[fun ω => f ω * 1] ∧
    variance (fun ω => f ω * (1 - b)) π < variance f π := by
-- proof
  constructor
  · simp [integral_mul_const, h₀]
  ·
    have : (fun ω => f ω * (1 - b)) = fun ω => (1 - b) * f ω := by
      ext ω
      ring
    rw [this, variance_const_mul]
    have hlt : (1 - b) ^ 2 < 1 := by nlinarith [h₁, h₂]
    have hpos : 0 < variance f π := lt_of_le_of_ne (variance_nonneg f π) (Ne.symm h₃)
    nlinarith


-- created on 2026-10-11
-- updated on 2026-10-17
