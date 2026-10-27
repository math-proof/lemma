import Mathlib.Probability.ConditionalProbability
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
Forgetting history: if `A` is independent of the recent state `B` and of the longer history `B ∩ C`,
then `P(A | B ∩ C) = P(A | B)`.
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
  (h₃ : π (A ∩ (B ∩ C)) = π A * π (B ∩ C))
  (h₄ : π B ≠ 0)
  (h₅ : π (B ∩ C) ≠ 0) :
-- imply
  π[A | B ∩ C] = π[A | B] := by
-- proof
  rw [cond_apply h₁, cond_apply h₀, Set.inter_comm (B ∩ C) A, Set.inter_comm B A]
  have hset : A ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x
    simp [and_assoc]
  have h₃' : π (A ∩ B ∩ C) = π A * π (B ∩ C) := by rw [← hset, h₃]
  rw [hset, h₃', h₂, mul_comm (π A) (π (B ∩ C)), mul_comm (π A) (π B)]
  rw [← mul_assoc, ENNReal.inv_mul_cancel h₅ (measure_ne_top π _), one_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel h₄ (measure_ne_top π _), one_mul]


-- created on 2023-04-05
-- updated on 2026-10-26
