import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
History irrelevance at every past index: each positive event `s i` that is independent of `A`
satisfies `P(A | s i) = P(A)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {A : Set Ω}
  {s : ι → Set Ω}
-- given
  (h₀ : ∀ i, MeasurableSet (s i))
  (h₁ : ∀ i, π (A ∩ s i) = π A * π (s i))
  (h₂ : ∀ i, π (s i) ≠ 0) :
-- imply
  ∀ i, π[A | s i] = π A := by
-- proof
  intro i
  rw [cond_apply (h₀ i), Set.inter_comm, h₁ i, mul_comm (π A) (π (s i)), ← mul_assoc,
    ENNReal.inv_mul_cancel (h₂ i) (measure_ne_top π _), one_mul]


-- created on 2026-10-11
-- updated on 2026-10-17
