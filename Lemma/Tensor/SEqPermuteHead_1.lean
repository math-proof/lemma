import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.List.EqRotate_1.of.LeLength_1
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.LtVal
import Lemma.Vector.EqGetS
import Lemma.List.EqAppendTake__Drop
import Lemma.List.ProdAppend.eq.MulProdS
open List Nat Vector Bool Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  X.permuteHead 1 ≃ X := by
-- proof
  by_cases h_s : s = []
  ·
    subst h_s
    unfold Tensor.permuteHead
    apply SEq.of.SEqDataS.Eq (by simp)
    simp
    apply SEq.of.All_EqGetS.Eq (by simp)
    intro t
    simp only [GetElem.getElem]
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (j := ⟨0, by simp⟩) (i := ⟨0, by simp⟩) (by simp)]
    unfold Tensor.rotate
    simp [EqGetS]
    simp only [GetElem.getElem]
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (j := ⟨0, by simp⟩) (i := ⟨0, by simp⟩) (by simp)]
    rw [GetTranspose.eq.Get.fin]
    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    simp
  ·
    have h_s := GtLength_0.of.Ne_Nil h_s
    have h_length : (s.take 1).length = 1 := by 
      simp
      omega
    unfold Tensor.permuteHead
    apply SEq.of.SEqDataS.Eq
    ·
      rw [EqRotate_1.of.LeLength_1 (by simp)]
      apply EqAppendTake__Drop
    ·
      simp
      apply SEqCast.of.SEq.Eq.Eq
      ·
        simp
      ·
        rw [EqRotate_1.of.LeLength_1 (by simp)]
        rw [EqAppendTake__Drop]
      ·
        apply SEq.of.All_EqGetS.Eq
        ·
          intro t
          have h_t := LtVal t
          let ⟨k', k, h_k'k⟩ := Any_EqAddMul.of.Lt_Mul h_t
          have h_k := LtVal k
          simp at h_k
          have h_k' := LtVal k'
          simp [EqRotate_1.of.LeLength_1] at h_k'
          simp [GetFlatten.eq.Get.of.Eq_AddMul h_k'k.symm]
          simp at h_t
          unfold Tensor.rotate
          simp
          simp only [GetElem.getElem]
          repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
          ·
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (j := ⟨0, by simp [h_length]⟩) (i := ⟨k', by simpa [h_length]⟩) (t := k') (by simp [h_length])]
            rw [GetTranspose.eq.Get.fin]
            repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            simp at h_k'k
            simp
            simp [h_k'k]
          ·
            simpa [h_length]
          ·
            simp [h_length]
            simp [EqRotate_1.of.LeLength_1]
        ·
          rw [EqRotate_1.of.LeLength_1 (by simp)]
          rw [MulProdS.eq.ProdAppend]
          rw [EqAppendTake__Drop]


-- created on 2025-10-20
