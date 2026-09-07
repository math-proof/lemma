import Lemma.Tensor.Eq.is.ToMatrix
import Lemma.Tensor.EqToMatrix0'0
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import sympy.matrices.expressions.matmul
open Matrix Tensor


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (A : Tensor α [l, n]) :
-- imply
  (0 : Tensor α [m, l]) @ A = (0 : Tensor α [m, n]) := by
-- proof
  apply Eq.of.ToMatrix
  apply Eq.trans (ToMatrixDot.eq.MulToMatrixS (0 : Tensor α [m, l]) A)
  apply Eq.trans (congrArg (fun M => HMul.hMul M A.toMatrix) EqToMatrix0'0)
  apply Eq.trans (Matrix.zero_mul A.toMatrix)
  exact EqToMatrix0'0.symm


-- created on 2026-09-07
