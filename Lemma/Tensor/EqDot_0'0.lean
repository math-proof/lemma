import Lemma.Tensor.Eq.is.ToMatrix
import Lemma.Tensor.EqToMatrix0'0
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import sympy.matrices.expressions.matmul
open Matrix Tensor


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (A : Tensor α [m, l]) :
-- imply
  A @ (0 : Tensor α [l, n]) = (0 : Tensor α [m, n]) := by
-- proof
  apply Eq.of.ToMatrix
  apply Eq.trans (ToMatrixDot.eq.MulToMatrixS A (0 : Tensor α [l, n]))
  apply Eq.trans (congrArg (HMul.hMul A.toMatrix) EqToMatrix0'0)
  apply Eq.trans (Matrix.mul_zero A.toMatrix)
  exact EqToMatrix0'0.symm


-- created on 2026-09-07
