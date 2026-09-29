import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma extreme_value_theorem
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h : a < b)
  (hc : ContinuousOn f (Set.Icc a b)) :
-- imply
  ∃ ξ ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, f z ≥ f ξ := by
-- proof
  obtain ⟨ξ, hξ, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr h.le) hc
  exact ⟨ξ, hξ, fun z hz => isMinOn_iff.mp hmin z hz⟩


-- created on 2026-09-27
