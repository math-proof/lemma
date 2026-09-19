import Lemma.Tensor.EqGetT
import torch.Tensor.permute
import sympy.matrices.dense
open scoped Matrix


@[main, comm]
private lemma main
-- given
  (X : Tensor α [m, n]) :
-- imply
  Xᵀ.toMatrix = (X.toMatrix)ᵀ := by
-- proof
  ext i j
  exact Tensor.EqGetT X j i


-- created on 2026-09-07
