import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma boundedness_theorem
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hc : ContinuousOn f (Set.Icc a b)) :
-- imply
  ∃ M, ∀ z ∈ Set.Icc a b, f z ≤ M := by
-- proof
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨M, fun z hz => hM (Set.mem_image_of_mem f hz)⟩


@[path]
private lemma extreme_value_theorem
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h : a ≤ b)
  (hc : ContinuousOn f (Set.Icc a b)) :
-- imply
  ∃ ξ ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, f z ≤ f ξ := by
-- proof
  obtain ⟨ξ, hξ, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr h) hc
  exact ⟨ξ, hξ, fun z hz => isMaxOn_iff.mp hmax z hz⟩


-- created on 2020-06-14
