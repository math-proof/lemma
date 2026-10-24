import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.GaussianSpace
open GaussianSpace ProbabilityTheory MeasureTheory
open MeasureTheory ProbabilityTheory Real


namespace GaussianSpace

/--
[stdGaussianDensity_eq_gaussianPDFReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianSpace.lean)
-/
@[path]
lemma stdGaussianDensity_eq_gaussianPDFReal
  {_n : ℕ}
  {t : ℝ} :
-- imply
  stdGaussianDensity t = gaussianPDFReal 0 1 t := by
-- proof
  simp only [stdGaussianDensity, gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]

end GaussianSpace

namespace GaussianSpace

/--
[integral_stdGaussianDensity_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianSpace.lean)
-/
@[path]
lemma integral_stdGaussianDensity_eq_one
  {_n : ℕ} :
-- imply
  ∫ t : ℝ, stdGaussianDensity t = 1 := by
-- proof
  have h : (fun t => stdGaussianDensity t) = gaussianPDFReal 0 1 := by
    ext t
    exact stdGaussianDensity_eq_gaussianPDFReal t
  rw [h]
  exact integral_gaussianPDFReal_eq_one 0 one_ne_zero

end GaussianSpace


-- created on 2026-10-23
