/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ExponentialIntegral/E1.lean -/


import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1.DLMF
import Lemma.Complex.SpecialFunctions.ExponentialIntegral.E1.DLMF

namespace Complex

example (z : ℂ) (hz : z ≠ 0) (hargLower : Real.pi / 2 ≤ |z.arg|)
    (hargUpper : |z.arg| < Real.pi) :
    ‖e1AsymptoticRemainder 2 z hz‖ ≤
      (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ :=
  principal_exponential_integral_e1_two_term_remainder_dlmf
    z hz hargLower hargUpper

/-- Regression: the raw kernel at `0` is `-γ` by junk values
(`ein 0 = 0`, `Complex.log 0 = 0`). -/
example : principalExponentialIntegralE1Raw 0 = -(Real.eulerMascheroniConstant : ℂ) :=
  principalExponentialIntegralE1Raw_zero

/-- Regression: each raw asymptotic term vanishes at `0` by junk division. -/
example (n : ℕ) : e1AsymptoticTermRaw n 0 = 0 :=
  e1AsymptoticTermRaw_zero n

/-- Regression: each raw partial sum vanishes at `0`. -/
example (n : ℕ) : e1AsymptoticPartialRaw n 0 = 0 :=
  e1AsymptoticPartialRaw_zero n

/-- Regression: the raw remainder at `0` is `-γ` by junk values. -/
example (n : ℕ) :
    e1AsymptoticRemainderRaw n 0 = -(Real.eulerMascheroniConstant : ℂ) :=
  e1AsymptoticRemainderRaw_zero n

end Complex
