import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Sliced Markov step, in the length-two case where the observed slice is the event `A`: `P(B | A) P(A | C) = P(A ∩ B | C)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {A B C : Set Ω}
-- given
  (h₀ : MeasurableSet A)
  (h₁ : MeasurableSet C)
  (h₂ : π (A ∩ C) ≠ 0)
  (h₃ : π[B | A] = π[B | A ∩ C]) :
-- imply
  π[B | A] * π[A | C] = π[A ∩ B | C] := by
-- proof
  rw [h₃]
  rw [cond_apply h₁, cond_apply (h₀.inter h₁), cond_apply h₁]
  have hset : C ∩ (A ∩ B) = (A ∩ C) ∩ B := by
    ext x
    simp [and_assoc, and_left_comm, and_comm]
  rw [hset]
  rw [Set.inter_comm C A]
  calc
    _ = (π C)⁻¹ * (π (A ∩ C) * ((π (A ∩ C))⁻¹ * π ((A ∩ C) ∩ B))) := by ac_rfl
    _ = (π C)⁻¹ * π ((A ∩ C) ∩ B) := by
      congr 1
      rw [← mul_assoc, ENNReal.mul_inv_cancel h₂ (measure_ne_top π _), one_mul]


-- created on 2026-10-11
-- updated on 2026-10-17
