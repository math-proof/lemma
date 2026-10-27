import Mathlib.Probability.ConditionalProbability
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
The product of successive conditional probabilities rebuilds the joint conditional.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {A B C : Set Ω}
-- given
  (h₀ : MeasurableSet A)
  (h₁ : MeasurableSet C)
  (h₂ : π (A ∩ C) ≠ 0) :
-- imply
  π[B | A ∩ C] * π[A | C] = π[A ∩ B | C] := by
-- proof
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


-- created on 2023-10-13
-- updated on 2026-10-26
