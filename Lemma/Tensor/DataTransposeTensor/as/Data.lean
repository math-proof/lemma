import Lemma.Nat.EqMod.of.Lt
import Lemma.List.TailPermute__Neg.eq.EraseIdx
import Lemma.List.ProdPermute.eq.Prod
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Tensor.EqGetS.of.Data.as.FlattenTransposeSplitAt_1
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteTail.eq.CastRotate.of.LeLength
import Lemma.Tensor.Permute__0.eq.Cast
import Lemma.Tensor.GetData.eq.GetDataGet.of.GtProd.GtLength_0
open List Tensor Vector Nat


@[main]
private lemma main
-- given
  (v : List.Vector α n) :
-- imply
  (⟨cast (congrArg (List.Vector α) (by simp)) v⟩ : Tensor α [n, 1])ᵀ.data ≃ v := by
-- proof
  apply SEq.of.All_EqGetS.Eq.fin
  .
    intro t
    have h_t := t.isLt
    conv_rhs at h_t =>
      simp
    simp [EqSwap_0'1] at h_t
    unfold Tensor.T
    unfold Tensor.transpose
    simp
    rw [Permute__0.eq.Cast]
    have h_permute := List.EqPermute__0 (0 : Fin (1 + 1)) (s := [n, 1])
    have := GetData.eq.GetDataGet.of.GtProd.GtLength_0.fin (i := t.val) (α := α) (s := (([n, 1].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)))
    simp at this
    rw [this]
    .
      have h_tail_permute := TailPermute__Neg.eq.EraseIdx (d := ⟨1, by grind⟩) (s := ([n, 1].permute (0 : Fin (1 + 1)) 0))
      simp at h_tail_permute
      have h_t : ↑t % (([n, 1].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)).tail.prod = t := by
        rw [h_tail_permute]
        simp [h_permute]
        apply EqMod.of.Lt h_t
      simp [h_t]
      have h_0 : ↑t / (([n, 1].permute (0 : Fin (1 + 1)) 0).permute (1 : Fin ([].length + 2)) (-1)).tail.prod = 0 := by
        simp
        right
        rw [h_tail_permute]
        simpa [h_permute]
      simp [h_0]
      sorry
    .
      rw [ProdPermute.eq.Prod]
      grind
  .
    simp [EqSwap_0'1]


-- created on 2026-04-07
