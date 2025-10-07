import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import Lemma.Algebra.DivMul.eq.Mul_Div
import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma main
-- given
  (x : ℂ) :
-- imply
  (I * x).exp = x.cos + I * x.sin := by
-- proof
  rw [Complex.sin, Complex.cos]
  rw [Mul_Div.eq.DivMul.comm]
  rw [MulMul.eq.Mul_Mul]
  simp
  rw [AddDivS.eq.DivAdd]
  simp
  rw [Mul.comm]


-- created on 2025-10-07
