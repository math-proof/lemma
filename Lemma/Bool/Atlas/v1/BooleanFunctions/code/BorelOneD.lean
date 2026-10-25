import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.BorelOneD
open MeasureTheory ProbabilityTheory Real Set GaussianStability


namespace GaussianStability

/--
[thresholdAtLevel_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BorelOneD.lean)
-/
@[path]
lemma thresholdAtLevel_range
  {t : ℝ}
  {x : ℝ} :
-- imply
  thresholdAtLevel t x ∈ Icc (-1 : ℝ) 1 := by
-- proof
  simp only [thresholdAtLevel]
  split_ifs <;> norm_num

end GaussianStability

namespace GaussianStability

/--
[thresholdFn_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BorelOneD.lean)
-/
@[path]
lemma thresholdFn_range
  {c : ℝ}
  {x : ℝ} :
-- imply
  thresholdFn c x ∈ Icc (-1 : ℝ) 1 := by
-- proof
  unfold thresholdFn
  exact thresholdAtLevel_range _ x
end GaussianStability



-- created on 2026-10-23
