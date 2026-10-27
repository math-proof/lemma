import Mathlib.Probability.ConditionalProbability
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
A positive joint and a positive condition give a positive conditional probability.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsFiniteMeasure π]
  {A B : Set Ω}
-- given
  (h₀ : MeasurableSet B)
  (h₁ : π (A ∩ B) ≠ 0) :
-- imply
  π[A | B] ≠ 0 := by
-- proof
  rw [cond_apply h₀, Set.inter_comm]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top π _)) h₁


-- created on 2023-03-22
-- updated on 2026-10-26
