import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.GaussianSpace.gaussianSpace.stdGaussianDensity_eq_gaussianPDFReal
open GaussianSpace ProbabilityTheory MeasureTheory Real Bool


/--
[integral_stdGaussianDensity_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianSpace.lean)
-/
@[path]
private lemma main :
-- imply
  ∫ t : ℝ, stdGaussianDensity t = 1 := by
-- proof
  have h : (fun t => stdGaussianDensity t) = gaussianPDFReal 0 1 := by
    ext t
    exact stdGaussianDensity_eq_gaussianPDFReal (t := t)
  simpa only [h] using integral_gaussianPDFReal_eq_one 0 one_ne_zero


lemma GaussianSpace.integral_stdGaussianDensity_eq_one :
-- imply
  ∫ t : ℝ, stdGaussianDensity t = 1 := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
