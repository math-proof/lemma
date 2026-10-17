import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
One-factor form of the expanded Bayes product:
`P(Y | X) = P(Y) · (P(Y | X) P(X) / P(Y)) / P(X)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsFiniteMeasure π]
  {X Y : Set Ω}
-- given
  (h₀ : π X ≠ 0)
  (h₁ : π Y ≠ 0) :
-- imply
  (π[Y | X]).toReal =
    (π Y).toReal * ((π[Y | X]).toReal * (π X).toReal / (π Y).toReal) / (π X).toReal := by
-- proof
  have hx : (π X).toReal ≠ 0 := (ENNReal.toReal_pos h₀ (measure_ne_top π X)).ne'
  have hy : (π Y).toReal ≠ 0 := (ENNReal.toReal_pos h₁ (measure_ne_top π Y)).ne'
  field_simp [hx, hy]


-- created on 2026-10-11
-- updated on 2026-10-17
