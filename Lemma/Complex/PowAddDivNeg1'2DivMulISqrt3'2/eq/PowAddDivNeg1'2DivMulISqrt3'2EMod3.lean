import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.AddDivNeg1'2DivMulISqrt3'2.ne.Zero
import Lemma.Complex.PowAddDivNeg1'2DivMulISqrt3'2'3.eq.One
open Complex


@[path]
private lemma main
  {d : ℤ} :
-- imply
  (-1 / 2 + Complex.I * √3 / 2 : ℂ) ^ d = (-1 / 2 + Complex.I * √3 / 2) ^ (d % 3) := by
-- proof
  have e : d = d % 3 + 3 * (d / 3) := by omega
  conv_lhs => rw [e, zpow_add₀ AddDivNeg1'2DivMulISqrt3'2.ne.Zero, zpow_mul]
  rw [show ((-1 / 2 + Complex.I * √3 / 2 : ℂ) ^ (3 : ℤ)) = 1 by rw [zpow_ofNat]; exact PowAddDivNeg1'2DivMulISqrt3'2'3.eq.One, one_zpow, mul_one]


-- created on 2026-10-07
