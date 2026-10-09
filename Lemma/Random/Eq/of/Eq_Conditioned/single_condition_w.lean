import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import sympy.stats.joint_rv
import sympy.Basic

open ProbabilityTheory MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x y z w : Ω → ℝ}
-- given
  (_hx : Measurable x) (_hy : Measurable y) (_hz : Measurable z) (_hw : Measurable w)
  (h : x ⟂ᵢ[π] (y, z) | w) :
-- imply
  x ⟂ᵢ[π] y | w := by
-- proof
  exact h.comp measurable_id measurable_fst


-- created on 2026-10-07
