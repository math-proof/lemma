/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/DLMF.lean -/

import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1.TwoTermRemainder
open Filter Set Topology MeasureTheory

noncomputable section

namespace Complex

/-- The `n = 2` outer-sector specialization of DLMF 6.12.1 and its remainder bound. -/
theorem principal_exponential_integral_e1_two_term_remainder_dlmf
    (z : ℂ) (hz : z ≠ 0) (hargLower : Real.pi / 2 ≤ |z.arg|)
    (hargUpper : |z.arg| < Real.pi) :
    ‖e1AsymptoticRemainder 2 z hz‖ ≤
      (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ := by
  rw [two_term_integral_remainder z hz hargUpper]
  exact integral_remainder_bound z hz hargLower hargUpper

end Complex
