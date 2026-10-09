import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.PowAddDivNeg1'2DivMulISqrt3'2'3.eq.One
open Complex


@[path]
private lemma main
  {d : ℤ} :
-- imply
  ((-1 / 2 + Complex.I * √3 / 2 : ℂ) ^ d) ^ 3 = 1 := by
-- proof
  rw [← zpow_natCast, ← zpow_mul, mul_comm d, zpow_mul, zpow_natCast, PowAddDivNeg1'2DivMulISqrt3'2'3.eq.One, one_zpow]


-- created on 2026-10-07
