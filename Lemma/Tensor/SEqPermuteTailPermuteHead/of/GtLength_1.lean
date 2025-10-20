import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.List.EqRotateRotate.of.Le_Length
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.LtVal
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.List.DropRotate.eq.Take.of.Le_Length
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.List.TakeRotate.eq.Drop.of.Le_Length
import Lemma.Nat.EqMod.of.Lt
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Nat.Gt_0.of.Gt
open Vector Tensor List Bool Nat


@[main]
private lemma main
-- given
  (h : s.length > 1)
  (X : Tensor α s) :
-- imply
  (X.permuteHead s.length).permuteTail s.length ≃ X := by
-- proof
  have h_0 := Gt_0.of.Gt h
  unfold Tensor.permuteTail Tensor.permuteHead
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    simp
    apply EqRotateRotate.of.Le_Length
    omega
  ·
    simp
    apply SEqCast.of.SEq.Eq.Eq
    ·
      rw [MulProdS.eq.ProdAppend]
    ·
      apply congrArg
      simp
      apply Eq_RotateRotate.of.Le_Length
      omega
    ·
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := LtVal t
        let ⟨k', k, h_k'k⟩ := Any_EqAddMul.of.Lt_Mul h_t
        have h_k := LtVal k
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_k'k.symm]
        unfold Tensor.rotate
        repeat rw [GetCast.eq.Get.of.Eq.Lt]
        ·
          simp
          simp at h_k
          let s₀ := (s.take s.length).rotate 1 ++ s.drop s.length
          let s' := s₀.drop (s₀.length - s.length)
          have h_rotate : s' = s.rotate 1 := by 
            unfold s' s₀
            simp
          have h_length : (s.length ⊓ s₀.length - 1) % s'.length = s.length - 1 := by 
            unfold s' s₀
            simp
          rw [Rotate.eq.AppendDrop__Take.of.Le_Length (n := s.length - 1) (by simp)] at h_k
          rw [← h_rotate, ← h_length] at h_k
          rw [ProdAppend.eq.MulProdS] at h_k
          let ⟨i, j, h_ij⟩ := Any_EqAddMul.of.Lt_Mul h_k
          rw [GetFlatten.eq.Get.of.Eq_AddMul h_ij.symm]
          simp [(show s₀.length = s.length by simp [s₀])] at h_ij
          simp [(show s'.length = s.length by simp [s', s₀])] at h_ij
          rw [GetTranspose.eq.Get]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
          simp [DropRotate.eq.Take.of.Le_Length (s := s) (n := 1) (by omega)]
          simp [ProdRotate.eq.Prod]
          simp [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)]
          have h_k' := LtVal k'
          simp at h_k'
          simp [h_k']
          have h_i := LtVal i
          conv_rhs at h_i =>
            simp [s', s₀]
          rw [DropRotate.eq.Take.of.Le_Length (by omega)] at h_i
          have h_i' := h_i
          rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)] at h_i
          have h_j := LtVal j
          conv_rhs at h_j =>
            simp [s', s₀]
          rw [TakeRotate.eq.Drop.of.Le_Length (by omega)] at h_j
          simp at h_j
          have h_prod : j * s[0] + i < (s.rotate 1).prod := by 
            simp [Rotate.eq.AppendDrop__Take.of.Le_Length (v := s) (n := 1) (by omega), ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)]
            apply AddMul.lt.Mul.of.Lt.Lt <;>
            ·
              assumption
          rw [GetCast.eq.Get.of.Eq.Lt]
          ·
            rw [GetFlatten.eq.Get.of.Eq_AddMul (j := ⟨0, by simp⟩) (i := ⟨j * s[0] + i, by simp_all⟩) (by simp)]
            rw [GetCast.eq.Get.of.Eq.Lt]
            ·
              rw [GetFlatten.eq.Get.of.Eq_AddMul (j := ⟨i, by simpa [EqMod.of.Lt h]⟩) (i := ⟨j, by simpa [EqMod.of.Lt h]⟩)]
              ·
                rw [GetTranspose.eq.Get]
                rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
                rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
                simp [EqMod.of.Lt h]
                simp [h_k'] at h_k'k
                simp [← h_k'k]
                simp [s', s₀] at h_ij
                rw [TakeRotate.eq.Drop.of.Le_Length (by omega)] at h_ij
                simp at h_ij
                simp_all
              ·
                simp [EqMod.of.Lt h]
                left
                rw [ProdTake_1.eq.Get_0.of.GtLength_0]
            ·
              rw [MulProdS.eq.ProdAppend]
              rw [AppendDrop__Take.eq.Rotate]
              simpa
            ·
              rw [MulProdS.eq.ProdAppend]
              apply congrArg
              simp
              rw [Rotate.eq.AppendDrop__Take]
          ·
            simp_all
          ·
            simp
        ·
          rw [MulProdS.eq.ProdAppend]
          convert h_k
          simp
          apply AppendDrop__Take.eq.Rotate.of.Le_Length
          simp
        ·
          rw [MulProdS.eq.ProdAppend]
        ·
          convert h_k
          simp
          apply AppendDrop__Take.eq.Rotate.of.Le_Length
          simp
        ·
          apply congrArg
          simp
          apply AppendDrop__Take.eq.Rotate.of.Le_Length
          simp
      ·
        simp
        rw [EqRotateRotate.of.Le_Length]
        omega


-- created on 2025-10-20
