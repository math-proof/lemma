import Lemma.Tensor.GetTranspose.eq.Get
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
  exact GetTranspose.eq.Get X j i


-- created on 2026-09-07
