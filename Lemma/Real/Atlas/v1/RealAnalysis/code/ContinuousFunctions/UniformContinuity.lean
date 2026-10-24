import Mathlib
import sympy.Basic
open Metric


namespace Real_Analysis

/--
[uniform_continuous_on_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/UniformContinuity.lean)
-/
@[path]
lemma uniform_continuous_on_iff
  {f : ℝ → ℝ}
  {S : Set ℝ} :
-- imply
  UniformContinuousOn f S ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, := by
-- proof
  simp only [Metric.uniformContinuousOn_iff, Real.dist_eq]

end Real_Analysis


-- created on 2026-10-23
