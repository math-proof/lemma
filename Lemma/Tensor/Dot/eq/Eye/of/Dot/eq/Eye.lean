import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Lemma.Tensor.Eq.is.ToMatrix
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import Lemma.Tensor.ToMatrixEye.eq.One
import sympy.matrices.expressions.special
import sympy.tensor.functions
open Tensor


@[main]
private lemma main
  [CommSemiring α] [CharZero α]
  {A B : Tensor α [n, n]}
-- given
  (h : A @ B = Tensor.eye (α := α) n) :
-- imply
  B @ A = Tensor.eye (α := α) n := by
-- proof
  apply Eq.of.ToMatrix
  apply Eq.trans (ToMatrixDot.eq.MulToMatrixS B A)
  apply Eq.trans _ (ToMatrixEye.eq.One (α := α)).symm
  apply (mul_eq_one_comm (a := A.toMatrix) (b := B.toMatrix)).mp
  apply Eq.trans (ToMatrixDot.eq.MulToMatrixS A B).symm
  apply Eq.trans (congrArg toMatrix h)
  apply ToMatrixEye.eq.One


-- created on 2026-09-05
