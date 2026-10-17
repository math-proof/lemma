import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
If `A` is independent of `B` and of `B ∩ C`, both positive, then conditioning on the joint `B ∩ C`
agrees with conditioning on `B` alone: both equal `P(A)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {A B C : Set Ω}
-- given
  (h₀ : MeasurableSet B)
  (h₁ : MeasurableSet (B ∩ C))
  (h₂ : π (A ∩ B) = π A * π B)
  (h₃ : π (A ∩ B ∩ C) = π A * π (B ∩ C))
  (h₄ : π B ≠ 0)
  (h₅ : π (B ∩ C) ≠ 0) :
-- imply
  π[A | B ∩ C] = π[A | B] := by
-- proof
  rw [cond_apply h₁, cond_apply h₀, Set.inter_comm (B ∩ C) A, Set.inter_comm B A]
  have hset : A ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x
    simp [and_assoc]
  rw [hset]
  rw [h₃, h₂, mul_comm (π A) (π (B ∩ C)), mul_comm (π A) (π B)]
  rw [← mul_assoc, ENNReal.inv_mul_cancel h₅ (measure_ne_top π _), one_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel h₄ (measure_ne_top π _), one_mul]


-- created on 2026-10-11
-- updated on 2026-10-17
