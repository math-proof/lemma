import Mathlib.Probability.Independence.Basic
import sympy.stats.joint_rv
import sympy.Basic

open ProbabilityTheory MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x y z w : Ω → ℝ}
-- given
  (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) (hw : Measurable w)
  (h : x ⟂ᵢ[π] (y, z) | w) :
-- imply
  x ⟂ᵢ[π] y | w := by
-- proof
  sorry


-- created on 2026-10-07
