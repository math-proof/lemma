import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Tensor.EqGetS.of.Data.as.FlattenTransposeSplitAt_1
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteTail.eq.CastRotate.of.LeLength
import Lemma.Tensor.Permute__0.eq.Cast
import Lemma.Vector.Eq.of.Eq_Cast.Eq
import sympy.tensor.tensor
open List Tensor Vector


@[main, fin]
private lemma main
-- given
  (X : Tensor α ((b :: bz) ++ [m, n]))
  (i : Fin b) :
-- imply
  have : i < Xᵀ.length := by
    sorry
  Xᵀ[i] ≃ X[i]ᵀ := by
-- proof
  unfold Tensor.T
  simp
  unfold Tensor.transpose
  sorry


-- created on 2026-07-03
