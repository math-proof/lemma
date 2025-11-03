import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.List.EqRotateRotate.of.Le_Length
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.LtVal
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetCast.eq.Get.of.Eq
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
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        have h_r := LtVal r
        simp at h_r
        rw [Rotate.eq.AppendDrop__Take.of.Le_Length (n := s.length - 1) (by simp)] at h_r
        rw [ProdAppend.eq.MulProdS] at h_r
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
        unfold Tensor.rotate
        simp [GetElem.getElem]
        repeat rw [GetCast.eq.Get.of.Eq.fin]
        ·
          let s₀ := (s.take s.length).rotate 1 ++ s.drop s.length
          let s' := s₀.drop (s₀.length - s.length)
          have h_rotate : s' = s.rotate 1 := by
            unfold s' s₀
            simp
          have h_length : (s.length ⊓ s₀.length - 1) % s'.length = s.length - 1 := by
            unfold s' s₀
            simp
          rw [← h_rotate, ← h_length] at h_r
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
          simp [show s₀.length = s.length by simp [s₀], show s'.length = s.length by simp [s', s₀]] at h_q'r'
          rw [GetTranspose.eq.Get.fin]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin]
          simp [DropRotate.eq.Take.of.Le_Length (s := s) (n := 1) (by omega)]
          simp [ProdRotate.eq.Prod]
          simp [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)]
          have h_q := LtVal q
          simp at h_q
          simp [h_q]
          have h_q' := LtVal q'
          conv_rhs at h_q' =>
            simp [s', s₀]
          rw [DropRotate.eq.Take.of.Le_Length (by omega)] at h_q'
          have := h_q'
          rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)] at h_q'
          have h_r' := LtVal r'
          conv_rhs at h_r' =>
            simp [s', s₀]
          rw [TakeRotate.eq.Drop.of.Le_Length (by omega)] at h_r'
          simp at h_r'
          have h_prod : r' * s[0] + q' < (s.rotate 1).prod := by
            simp [Rotate.eq.AppendDrop__Take.of.Le_Length (s := s) (n := 1) (by omega), ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)]
            apply AddMul.lt.Mul.of.Lt.Lt <;>
            ·
              assumption
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (j := ⟨0, by simp⟩) (i := ⟨r' * s[0] + q', by simp_all⟩) (by simp)]
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (j := ⟨q', by simpa [EqMod.of.Lt h]⟩) (i := ⟨r', by simpa [EqMod.of.Lt h]⟩)]
              ·
                rw [GetTranspose.eq.Get.fin]
                rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin]
                simp [EqMod.of.Lt h]
                simp [h_q] at h_qr
                simp [h_qr]
                simp [s', s₀] at h_q'r'
                rw [TakeRotate.eq.Drop.of.Le_Length (by omega)] at h_q'r'
                simp at h_q'r'
                simp_all
              ·
                simp [EqMod.of.Lt h]
                left
                rw [ProdTake_1.eq.Get_0.of.GtLength_0]
            ·
              rw [MulProdS.eq.ProdAppend]
              apply congrArg
              simp
              rw [Rotate.eq.AppendDrop__Take]
          ·
            simp
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [← Rotate.eq.AppendDrop__Take]
      ·
        simp
        rw [EqRotateRotate.of.Le_Length]
        omega


-- created on 2025-10-20
