import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Finset.Prod.eq.MulProdS
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.EraseIdxAppend.eq.AppendEraseIdx.of.GtLength
import Lemma.List.EraseIdxRotate.eq.Append_EraseIdxTake.of.LeLength_Add.GeLength
import Lemma.List.GetRotate.eq.Get_0.of.Gt_0.GeLength
import Lemma.List.Get_0.dvd.Prod.of.GtLength_0
import Lemma.List.LengthRotate.eq.Length
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.Prod.eq.MulProdTail.of.GtLength_0
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTail.eq.DivProd.of.GtLength_0.Gt_0
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.TakeRotate.eq.Tail
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivAddMul.of.Lt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtAddMul.of.Lt.Lt_Div.Dvd
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqPermuteHeadS.of.Eq
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Tensor.SEqSelectS.of.SEq.EqValS.EqValS
import Lemma.Tensor.Select_0.as.Get.of.Lt_Get_0.GtLength_0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin Finset List Nat Tensor Vector


@[main]
private lemma main
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_s : s.length > 0)
  (h_k : k < s[0])
  (X : Tensor α s) :
-- imply
  have h_s_length : s.length - 1 < (s.rotate 1).length := by rw [LengthRotate.eq.Length]; omega
  have h_rotate : (s.rotate 1)[s.length - 1] = s[0] := by rw [GetRotate.eq.Get_0.of.Gt_0.GeLength (by omega) (by omega)]
  have h_k_rotate : k < (s.rotate 1)[s.length - 1] := by rwa [h_rotate]
  (X.permuteHead s.length).select ⟨s.length - 1, by simpa⟩ ⟨k, by simpa⟩ ≃ X.get ⟨k, by rwa [← Length.eq.Get_0.of.GtLength_0 (by omega) X] at h_k⟩ := by
-- proof
  if h_s : s.length = 1 then
    simp
    symm
    apply SEq.trans (Get.as.Select_0.of.Lt_Get_0.GtLength_0 (by omega) h_k X)
    apply SEqSelectS.of.SEq.EqValS.EqValS
    ·
      symm
      apply SEq.trans (SEqPermuteHeadS.of.Eq X h_s)
      apply SEqPermuteHead_1
    ·
      grind
    ·
      simp
  else
    have h_s : s.length > 1 := by omega
    intro h_s_length h_rotate h_k_rotate
    unfold permuteHead
    simp
    apply SEq.of.SEqDataS.Eq
    ·
      rw [EraseIdxAppend.eq.AppendEraseIdx.of.GtLength (by simpa)]
      simp
      rw [EraseIdxRotate.eq.Append_EraseIdxTake.of.LeLength_Add.GeLength (by simpa) (by omega)]
      simp
      right
      constructor
      repeat grind
    ·
      rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, ?_⟩) (by omega)]
      ·
        rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
          rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength _ h_k_rotate]
          grind
        ·
          simp
        ·
          apply SEq.of.All_EqGetS.Eq.fin
          ·
            intro t
            have h_t := t.isLt
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
            let ⟨h_q_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
            have h_s_drop : (s.rotate 1).drop (s.length - 1 + 1) = [] := by
              simp [EqAddSub.of.Ge (show s.length ≥ 1 by omega)]
            have h_r := r.isLt
            simp [h_s_drop] at h_q_div h_r
            have h_q := q.isLt
            simp at h_q
            rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength _ h_k_rotate] at h_q
            rw [TakeRotate.eq.Tail] at h_q
            rw [ProdTail.eq.DivProd.of.GtLength_0.Gt_0 (by grind) (by grind)] at h_q
            simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
            rw [GetGetSlice.eq.Get.of.GtGet.GtLength]
            ·
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              rw [GetCast.eq.Get.of.Eq.fin (by simp)]
              simp
              have h_lt : (↑q * (s.rotate 1)[s.length - 1]'(by grind) + k) * ((s.rotate 1).drop (s.length - 1 + 1)).prod + ↑r < ((s.take s.length).rotate 1).prod * (s.drop s.length).prod := by
                simp [h_r, h_rotate, h_s_drop]
                rw [ProdRotate.eq.Prod]
                apply LtAddMul.of.Lt.Lt_Div.Dvd _ h_q h_k
                apply Get_0.dvd.Prod.of.GtLength_0
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
              have h_q' := q'.isLt
              simp [ProdRotate.eq.Prod] at h_q'
              have h_r' := r'.isLt
              simp at h_r'
              let ⟨h_q'_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              unfold Tensor.rotate
              simp
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                have h_s_mod : 1 % s.length = 1 := EqMod.of.Lt h_s
                have h_q' : q' < ((s.take s.length).drop (1 % (s.take s.length).length)).prod * ((s.take s.length).take (1 % (s.take s.length).length)).prod := by
                  simp [h_s_mod]
                  rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)]
                  rwa [← Prod.eq.MulProdTail.of.GtLength_0]
                let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_q'
                let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                simp at h_q'_div h_qₐ_div h_rₐ_mod
                simp [h_r, h_rotate, h_s_drop, h_q_div] at h_q'_div
                simp [h_q'_div] at h_qₐ_div h_rₐ_mod
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                apply congrArg
                simp [h_r']
                simp [h_qₐ_div, h_rₐ_mod]
                rw [h_s_mod]
                rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)]
                simp [EqMod.of.Lt h_k]
                apply EqDivAddMul.of.Lt h_k
              ·
                simp
                rw [ProdRotate.eq.Prod]
                rw [MulProdS.eq.Prod.comm]
            ·
              simpa
          ·
            simp
            rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength _ h_k_rotate]
            rw [Drop.eq.Nil.of.LeLength (by grind)]
            simp [TakeRotate.eq.Tail]
      ·
        assumption


-- created on 2026-04-09
-- updated on 2026-04-16
