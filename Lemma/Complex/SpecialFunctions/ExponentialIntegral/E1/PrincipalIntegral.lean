import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1.PrincipalIntegral
open Filter Set Topology MeasureTheory
open scoped ENNReal NNReal
open Complex


/--
[principal_e1_integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean)
-/
@[path]
private lemma principal_e1_integral_eq
  {z : ℂ}
-- given
  (hz : z ≠ 0)
  (harg : |z.arg| < Real.pi) :
-- imply
  principalExponentialIntegralE1 z hz =
    Complex.exp (-z) *
    ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) / ((t : ℂ) + z) := by
-- proof
  apply Complex.principal_e1_integral z hz harg


-- created on 2026-10-20
