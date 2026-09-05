import Mathlib.Data.Matrix.Mul
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.Mul
import sympy.matrices.dense
open Tensor


@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (X : Tensor α [m, l])
  (Y : Tensor α [l, n]) :
-- imply
  (X @ Y).toMatrix = X.toMatrix * Y.toMatrix := by
-- proof
  ext i j
  apply Eq.trans (GetDot.eq.Sum_MulGetS X Y i j)
  apply Eq.trans _ (Matrix.mul_apply (M := X.toMatrix) (N := Y.toMatrix) (i := i) (k := j)).symm
  apply Finset.sum_congr rfl
  intro k _
  apply Tensor.Mul


-- created on 2026-09-05
