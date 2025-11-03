import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.EraseIdx_Succ.eq.Cons_EraseIdxTail.of.Lt_LengthTail
import Lemma.List.GetAppend.eq.Get.of.Lt_Length
import Lemma.List.GetRotate.eq.Ite.of.Le_Length.Lt_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.List.Prod.eq.Mul_ProdEraseIdx.of.GtLength
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TailPermute.eq.PermuteEraseIdx.of.GtLength_1
import Lemma.List.TailRotateTake.eq.RotateTakeEraseIdx.of.GtLength_1
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtAddMul.of.Lt.Lt.Eq
import Lemma.Nat.LtVal
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.GetEllipsis_0.eq.Cast_Get.of.GtLength_0.Lt_Get_0
import Lemma.Tensor.LengthPermuteHead.eq.Get_1.of.GtLength_1.Gt_1
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
  {k : ℕ}
-- given
  (h : s.length > 1)
  (h_k : k < s[1])
  (X : Tensor α s) :
-- imply
  (X.permuteHead (d + 1)).get ⟨k, by rwa [LengthPermuteHead.eq.Get_1.of.GtLength_1.Gt_1 (by linarith [NeZero.pos d]) h]⟩ ≃ (X.getEllipsis ⟨1, by grind⟩ ⟨k, h_k⟩).permuteHead d := by
-- proof
  have h_d := NeZero.pos d
  unfold permuteHead
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    rw [TailAppend.eq.AppendTail.of.GtLength_0]
    ·
      rw [DropEraseIdx.eq.Drop.of.Le (by omega)]
      simp
      apply TailRotateTake.eq.RotateTakeEraseIdx.of.GtLength_1 h
    ·
      simp
      omega
  ·
    simp
    rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, ?_⟩)]
    ·
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        rw [MulProdS.eq.ProdAppend]
      ·
        simp
        apply SEq.of.All_EqGetS.Eq
        ·
          intro t
          have h_t := LtVal t
          simp only [GetElem.getElem]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [GetCast.eq.Get.of.Eq.fin]
          simp at h_t ⊢
          simp [TailAppend.eq.AppendTail.of.GtLength_0 (show ((s.take (d + 1)).rotate 1).length > 0 by simp; omega)] at h_t ⊢
          simp [TailRotateTake.eq.RotateTakeEraseIdx.of.GtLength_1 h] at h_t ⊢
          simp [ProdRotate.eq.Prod]
          simp only [← DropEraseIdx.eq.Drop.of.Le (i := 1) (j := d) (by omega)] at h_t ⊢
          simp
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          have h_q := LtVal q
          have h_r := LtVal r
          simp [ProdRotate.eq.Prod] at h_t
          let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
          have h_lt : k * (s.eraseIdx 1).prod + ↑t < ((s.take (d + 1)).rotate 1).prod * (s.drop (d + 1)).prod := by
            simp [ProdRotate.eq.Prod]
            rw [Prod.eq.Mul_ProdEraseIdx.of.GtLength h]
            exact AddMul.lt.Mul.of.Lt.Lt h_k h_t
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
          have h_q' := LtVal q'
          simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q' h_q
          let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          unfold Tensor.rotate
          simp
          repeat rw [GetCast.eq.Get.of.Eq.fin]
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
          have h_qₐ := LtVal qₐ
          have h_rₐ := LtVal rₐ
          simp at h_qₐ h_rₐ
          let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q'
          have h_qₑ := LtVal qₑ
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          repeat rw [GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          unfold Tensor.getEllipsis
          simp
          rw [DataCast.eq.Cast_Data.of.Eq]
          ·
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              rw [DataFromVector.eq.FlattenMapData]
              have h_lt : (↑rₐ * (((s.eraseIdx 1).take d).drop (1 % (d ⊓ (s.eraseIdx 1).length))).prod + ↑qₐ) * ((s.eraseIdx 1).drop d).prod + ↑r < (s.headD 1) * (s.tail.eraseIdx 0).prod := by
                sorry
              let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
              rw [GetEllipsis_0.eq.Cast_Get.of.GtLength_0.Lt_Get_0]
              rw [DataCast.eq.Cast_Data.of.Eq (by simp)]
              simp [GetCast.eq.Get.of.Eq.fin]
              sorry
            ·
              rw [EraseIdx_Succ.eq.Cons_EraseIdxTail.of.Lt_LengthTail]
              simp
              omega
          ·
            rw [EraseIdx_Succ.eq.Cons_EraseIdxTail.of.Lt_LengthTail]
            simp
            omega
          repeat {
            rw [MulProdS.eq.ProdAppend]
            rw [Rotate.eq.AppendDrop__Take]
          }
        ·
          rw [MulProdS.eq.ProdAppend]
          apply congrArg
          rw [← Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (by omega)]
          have := Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (s := s.eraseIdx 1) (by rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by omega)]; omega) (d - 1)
          rw [EqAddSub.of.Ge (by omega)] at this
          rw [← this]
          simp
          exact TailPermute.eq.PermuteEraseIdx.of.GtLength_1.pos h
    ·
      simp
      omega
    ·
      rw [GetAppend.eq.Get.of.Lt_Length]
      ·
        rw [GetRotate.eq.Ite.of.Le_Length.Lt_Length]
        ·
          simp
          split_ifs
          ·
            assumption
          ·
            omega
        repeat {
          simp
          omega
        }
      ·
        simp
        omega


-- created on 2025-11-02
-- updated on 2025-11-03
