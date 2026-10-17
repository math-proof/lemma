import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsFiniteMeasure π]
  {s t : Set Ω}
-- given
  (h₀ : MeasurableSet s)
  (h₁ : MeasurableSet t)
  (h₂ : π s ≠ 0) :
-- imply
  (π[t | s]).toReal = (π[s | t]).toReal * (π t).toReal / (π s).toReal := by
-- proof
  have h₃ : (π s).toReal ≠ 0 := (ENNReal.toReal_pos h₂ (measure_ne_top π s)).ne'
  rw [cond_eq_inv_mul_cond_mul (μ := π) h₀ h₁, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  field_simp [h₃]


-- created on 2020-11-28
-- updated on 2026-10-17
