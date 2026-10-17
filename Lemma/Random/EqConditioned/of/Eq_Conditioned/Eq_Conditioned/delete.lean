import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Deleting an independent condition: `P(A | B) = P(A)` when `A` is independent of `B`.
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


-- created on 2026-10-11
-- updated on 2026-10-17
