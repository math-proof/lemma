import Lemma.Tensor.GetDite.eq.Get.of.Not
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.LengthTranspose.eq.Length.of.GtLength_2
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Tensor.EqGetS.of.Data.as.FlattenTransposeSplitAt_1
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteTail.eq.CastRotate.of.LeLength
import Lemma.Tensor.Permute__0.eq.Cast
import Lemma.Vector.Eq.of.Eq_Cast.Eq
open List Tensor Vector Bool


@[main, fin]
private lemma main
-- given
  (X : Tensor α ((b :: bz) ++ [m, n]))
  (i : Fin b) :
-- imply
  have : i < Xᵀ.length := by
    rw [LengthTranspose.eq.Length.of.GtLength_2]
    repeat grind
  Xᵀ[i] ≃ X[i]ᵀ := by
-- proof
  simp [GetElem.getElem]
  unfold Tensor.T
  simp
  unfold Tensor.transpose
  simp
  apply SEq_Cast.of.SEq.Eq
  .
    simp
    rw [List.Swap.eq.PermutePermute.of.Lt.GtLength]
    .
      simp
      repeat rw [List.EqPermuteS.of.Eq.EqValS.Eq]
      .
        rfl
      .
        simp
      .
        simp
      .
        rfl
      .
        rfl
    .
      grind
    .
      grind
  .
    split_ifs with h
    .
      omega
    .
      repeat rw [Tensor.GetDite.eq.Get.of.Not.fin (by grind)]
      sorry


-- created on 2026-07-03
