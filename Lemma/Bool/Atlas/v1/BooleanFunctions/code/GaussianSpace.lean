import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.GaussianSpace
open GaussianSpace ProbabilityTheory MeasureTheory


/--
[stdGaussianDensity_eq_gaussianPDFReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianSpace.lean)
-/
@[path]
private lemma stdGaussianDensity_eq_gaussianPDFReal_eq
  {_n : ℕ}
  {t : ℝ} :
-- imply
  stdGaussianDensity t = gaussianPDFReal 0 1 t := by
-- proof
  apply GaussianSpace.stdGaussianDensity_eq_gaussianPDFReal t

/--
[integral_stdGaussianDensity_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianSpace.lean)
-/
@[path]
private lemma integral_stdGaussianDensity_eq_one_eq
  {_n : ℕ} :
-- imply
  ∫ t : ℝ, stdGaussianDensity t = 1 := by
-- proof
  apply GaussianSpace.integral_stdGaussianDensity_eq_one


-- created on 2026-10-23
