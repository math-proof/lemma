import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.GaussianSpace
open GaussianSpace ProbabilityTheory MeasureTheory Real


/--
[stdGaussianDensity_eq_gaussianPDFReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianSpace.lean)
-/
@[path]
private lemma main
  {t : ℝ} :
-- imply
  stdGaussianDensity t = gaussianPDFReal 0 1 t := by
-- proof
  simp only [stdGaussianDensity, gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]


lemma GaussianSpace.stdGaussianDensity_eq_gaussianPDFReal
  {t : ℝ} :
-- imply
  stdGaussianDensity t = gaussianPDFReal 0 1 t := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
