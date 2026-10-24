import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1.DLMF
open Filter Set Topology MeasureTheory
open Complex


namespace Complex

/--
[principal_exponential_integral_e1_two_term_remainder_dlmf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/DLMF.lean)
-/
@[path]
lemma principal_exponential_integral_e1_two_term_remainder_dlmf
  {z : ℂ}
-- given
  (hz : z ≠ 0)
  (hargLower : Real.pi / 2 ≤ |z.arg|)
  (hargUpper : |z.arg| < Real.pi) :
-- imply
  ‖e1AsymptoticRemainder 2 z hz‖ ≤
    (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ := by
-- proof
  rw [two_term_integral_remainder z hz hargUpper]
  exact integral_remainder_bound z hz hargLower hargUpper

end Complex


-- created on 2026-10-20
-- updated on 2026-10-23
