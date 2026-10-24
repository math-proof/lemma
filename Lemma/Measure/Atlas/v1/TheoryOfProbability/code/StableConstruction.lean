import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.StableConstruction
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal


namespace ProbabilityTheory

/--
[measureConv_dirac_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StableConstruction.lean)
-/
@[path]
lemma measureConv_dirac_zero
-- imply
  measureConv (Measure.dirac (0 : ℝ)) (Measure.dirac (0 : ℝ)) = Measure.dirac 0 := by
-- proof
  simp [measureConv, Measure.dirac_prod_dirac]

end ProbabilityTheory


-- created on 2026-10-23
