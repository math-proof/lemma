import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import Lemma.Algebra.DivMul.eq.Mul_Div
import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.DivAdd.eq.AddDivS
open Algebra


@[main]
private lemma complex
  {x : ℂ} :
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


@[main]
private lemma main
  {x : ℝ} :
-- imply
  (I * x).exp = cos x + I * sin x := by
-- proof
  have h_cos : cos x = (x : ℂ).cos := by simp
  have h_sin : sin x = (x : ℂ).sin := by simp
  rw [h_cos, h_sin]
  exact complex (x := x)


-- created on 2025-01-05
