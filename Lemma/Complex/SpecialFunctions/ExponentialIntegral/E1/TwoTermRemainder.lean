import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1.TwoTermRemainder
open Filter Set Topology MeasureTheory
open Complex


/--
[two_term_integral_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/TwoTermRemainder.lean)
-/
@[path]
private lemma two_term_integral_remainder_eq
  {z : ℂ}
-- given
  (hz : z ≠ 0)
  (harg : |z.arg| < Real.pi) :
-- imply
  e1AsymptoticRemainder 2 z hz =
    Complex.exp (-z) / z^2 *
    ∫ t : ℝ in Ioi 0,
    (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z) := by
-- proof
  apply Complex.two_term_integral_remainder z hz harg


-- created on 2026-10-20
