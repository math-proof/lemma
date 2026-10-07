import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.AddDivNeg1'2DivMulISqrt3'2.eq.ExpMulDivMul2Pi3I
open Complex


@[main]
private lemma main :
-- imply
  (-1 / 2 + Complex.I * √3 / 2 : ℂ) ^ 3 = 1 := by
-- proof
  rw [AddDivNeg1'2DivMulISqrt3'2.eq.ExpMulDivMul2Pi3I, ← Complex.exp_nat_mul]
  have : ((3 : ℕ) : ℂ) * (↑(2 * π / 3) * Complex.I) = 2 * π * Complex.I := by push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]


-- created on 2026-10-07
