import Lemma.Tensor.EqGetT
import Notation.Data.Holor.Permute
import Instance.LinearAlgebra.Matrix.Dense
open scoped Matrix


@[path, comm]
private lemma main
-- given
  (X : Tensor α [m, n]) :
-- imply
  Xᵀ.toMatrix = (X.toMatrix)ᵀ := by
-- proof
  ext i j
  exact Tensor.EqGetT X j i


-- created on 2026-09-07
