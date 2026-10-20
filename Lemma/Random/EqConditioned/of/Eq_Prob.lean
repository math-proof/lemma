import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
If `A` is independent of `B` and `B` has positive probability, conditioning on `B` does not change `P(A)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {A B : Set Ω}
-- given
  (h₀ : MeasurableSet B)
  (h₁ : π (A ∩ B) = π A * π B)
  (h₂ : π B ≠ 0) :
-- imply
  π[A | B] = π A := by
-- proof
  rw [cond_apply h₀, Set.inter_comm, h₁, mul_comm (π A) (π B), ← mul_assoc,
    ENNReal.inv_mul_cancel h₂ (measure_ne_top π _), one_mul]


-- created on 2023-03-23
-- updated on 2026-10-17
