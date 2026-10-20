import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1.EulerConstantNormalization
open Filter Set Topology MeasureTheory
open Complex


/--
[euler_constant_normalization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/EulerConstantNormalization.lean)
-/
@[path]
private lemma euler_constant_normalization_eq
  {x : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  principalExponentialIntegralE1 (x : ℂ)
    (Complex.ofReal_ne_zero.mpr hx.ne') =
    Complex.exp (-(x : ℂ)) *
    ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) / ((t : ℂ) + x) := by
-- proof
  apply Complex.euler_constant_normalization x hx


-- created on 2026-10-20
