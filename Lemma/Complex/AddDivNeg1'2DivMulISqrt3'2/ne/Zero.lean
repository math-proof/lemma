import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.AddDivNeg1'2DivMulISqrt3'2.eq.ExpMulDivMul2Pi3I
open Complex


@[main]
private lemma main :
-- imply
  (-1 / 2 + Complex.I * √3 / 2 : ℂ) ≠ 0 := by
-- proof
  rw [AddDivNeg1'2DivMulISqrt3'2.eq.ExpMulDivMul2Pi3I]
  exact Complex.exp_ne_zero _


-- created on 2026-10-07
