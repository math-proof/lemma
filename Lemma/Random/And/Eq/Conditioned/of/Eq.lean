import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Both factors of an independent joint stay unchanged when conditioned on an independent event `C`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {A B C : Set Ω}
-- given
  (h₀ : MeasurableSet C)
  (h₁ : π (A ∩ C) = π A * π C)
  (h₂ : π (B ∩ C) = π B * π C)
  (h₃ : π C ≠ 0) :
-- imply
  π[A | C] = π A ∧ π[B | C] = π B := by
-- proof
  constructor
  · rw [cond_apply h₀, Set.inter_comm, h₁, mul_comm (π A) (π C), ← mul_assoc,
      ENNReal.inv_mul_cancel h₃ (measure_ne_top π _), one_mul]
  · rw [cond_apply h₀, Set.inter_comm, h₂, mul_comm (π B) (π C), ← mul_assoc,
      ENNReal.inv_mul_cancel h₃ (measure_ne_top π _), one_mul]


-- created on 2023-03-23
-- updated on 2026-10-17
