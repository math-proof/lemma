import Mathlib.Probability.ConditionalProbability
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
A third conditioning variable that is independent of `A` can be ignored: `P(A | B) = P(A)`.
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


-- created on 2021-07-15
-- updated on 2026-10-26
