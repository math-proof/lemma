import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
One-step chain rule on a probability space: `P(A ∩ B) = P(B | A) P(A)` whenever `A` is positive.
This is the length-two case of `P(s[:n]) = ∏ P(s[k] | s[:k])`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {A B : Set Ω}
-- given
  (h₀ : MeasurableSet A)
  (h₁ : π A ≠ 0) :
-- imply
  π[B | A] * π A = π (A ∩ B) := by
-- proof
  rw [cond_apply h₀, mul_assoc, mul_comm (π (A ∩ B)) (π A), ← mul_assoc,
    ENNReal.inv_mul_cancel h₁ (measure_ne_top π _), one_mul]


-- created on 2026-10-11
-- updated on 2026-10-17
