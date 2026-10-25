import Mathlib
import sympy.Basic
import Def.v1.Atlas.RealAnalysis.code.ContinuousFunctions.Continuity
open ContinuousFunctions


namespace ContinuousFunctions

/--
[continuous_at_iff_eps_delta](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Continuity.lean)
-/
@[path]
lemma continuous_at_iff_eps_delta
  {f : ℝ → ℝ}
  {S : Set ℝ}
  {c : ℝ}
-- given
  (_hc : c ∈ S) :
-- imply
  ContinuousWithinAt f S c ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, := by
-- proof
  rw [Metric.continuousWithinAt_iff]
  simp only [Real.dist_eq]

end ContinuousFunctions

namespace ContinuousFunctions

/--
[continuous_on_Icc_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Continuity.lean)
-/
@[path]
lemma continuous_on_Icc_bounded
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (_hab : a ≤ b)
  (hf : ContinuousOn f (Set.Icc a b)) :
-- imply
  ∃ B : ℝ, ∀ x ∈ Set.Icc a b, := by
-- proof
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨C, fun x hx => by rw [← Real.norm_eq_abs]; exact hC x hx⟩

end ContinuousFunctions

namespace ContinuousFunctions

/--
[extreme_value_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Continuity.lean)
-/
@[path]
lemma extreme_value_theorem
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a < b)
  (hf : ContinuousOn f (Set.Icc a b)) :
-- imply
  (∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x) ∧ (∃ d ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f d) := by
-- proof
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr (le_of_lt hab)
  exact ⟨isCompact_Icc.exists_isMinOn hne hf, isCompact_Icc.exists_isMaxOn hne hf⟩

end ContinuousFunctions


-- created on 2026-10-23
