import Mathlib.Probability.Kernel.Basic
import sympy.Basic
open ProbabilityTheory


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  {κ₁ κ₂ : Kernel α β}
-- given
  (h : κ₁ = κ₂) :
-- imply
  ∀ a, κ₁ a = κ₂ a := by
-- proof
  intro a
  rw [h]


-- created on 2026-09-18
