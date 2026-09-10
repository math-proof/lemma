import Lemma.Tensor.EqGetT
import sympy.matrices.dense
open Matrix Tensor


@[main, comm]
private lemma main
-- given
  (X : Tensor α [m, n]) :
-- imply
  Xᵀ.toMatrix = X.toMatrixᵀ := by
-- proof
  ext i j
  exact EqGetT X j i


-- created on 2026-09-07
