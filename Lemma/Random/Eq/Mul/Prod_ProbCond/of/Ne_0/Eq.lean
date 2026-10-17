import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Bayes with one feature: `P(Y | X) = P(X | Y) P(Y) / P(X)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsFiniteMeasure π]
  {X Y : Set Ω}
-- given
  (h₀ : MeasurableSet X)
  (h₁ : MeasurableSet Y)
  (h₂ : π X ≠ 0) :
-- imply
  (π[Y | X]).toReal = (π[X | Y]).toReal * (π Y).toReal / (π X).toReal := by
-- proof
  have h₃ : (π X).toReal ≠ 0 := (ENNReal.toReal_pos h₂ (measure_ne_top π X)).ne'
  rw [cond_eq_inv_mul_cond_mul (μ := π) h₀ h₁, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  field_simp [h₃]


-- created on 2026-10-11
-- updated on 2026-10-17
