import Lemma.List.GetRotate.eq.Get.of.GtLength.Gt_0
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.List.ProdDrop.eq.Get.of.GtLength_0
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.List.Get.dvd.Prod.of.GtLength
import Lemma.Nat.EqDiv_Div.of.Ne_0.Dvd
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Finset.Prod.eq.MulProdS
import Lemma.List.ProdDropLast.eq.DivProd.of.GtLength_0.Gt_0
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.DropLast.dvd.Prod
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.Prod.eq.MulProdTail.of.GtLength_0
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTail.eq.DivProd.of.GtLength_0.Gt_0
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.TailRotate.eq.DropLast.of.GtLength_0
import Lemma.List.TakeRotate.eq.Tail
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivAddMul.of.Lt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtAddMul.of.Lt.Lt_Div.Dvd
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Tensor.LengthPermuteTail.eq.Get.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqPermuteTailS.of.Eq
import Lemma.Tensor.SEqPermuteTail_1
import Lemma.Tensor.SEqSelectS.of.SEq.Eq
import Lemma.Tensor.Select_0.as.Get.of.Lt_Get_0.GtLength_0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin Finset List Nat Tensor Vector


@[main]
private lemma main
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_s : s.length > 0)
  (h_k : k < s[s.length - 1])
  (X : Tensor α s) :
-- imply
  (X.permuteTail s.length).get ⟨k, by rwa [LengthPermuteTail.eq.Get.of.GtLength_0 h_s]⟩ ≃ X.select ⟨s.length - 1, by grind⟩ ⟨k, by grind⟩ := by
-- proof
  if h_s : s.length = 1 then
    simp
    symm
    apply SEq.trans (SEqSelectS.of.SEq.Eq (show ⟨s.length - 1, by grind⟩ = ⟨0, by grind⟩ by grind) (by rfl) (X := X) (i := ⟨k, by grind⟩) (i' := ⟨k, by grind⟩))
    apply SEq.trans (Select_0.as.Get.of.Lt_Get_0.GtLength_0 (by omega) (show k < s[0] by grind) X)
    apply SEqGetS.of.SEq.GtLength.fin
    symm
    apply SEq.trans (SEqPermuteTailS.of.Eq X h_s)
    apply SEqPermuteTail_1
  else
    have h_s : s.length > 1 := by omega
    unfold permuteTail
    simp
    apply SEq.of.SEqDataS.Eq
    ·
      simp
      rw [TailRotate.eq.DropLast.of.GtLength_0 (by omega)]
    ·
      rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, ?_⟩) (by grind)]
      ·
        rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          simp
          rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength _ h_k]
          simp [EqAddSub.of.Ge (show s.length ≥ 1 by omega)]
          rw [List.DropLast.eq.Take_SubLength_1]
        ·
          apply SEq.of.All_EqGetS.Eq.fin
          ·
            intro t
            have h_t := t.isLt
            simp at h_t
            rw [List.TailRotate.eq.Take.of.GtLength_0 (by omega)] at h_t
            simp
            have h_t : t < ((⟨↑k, ↑(s.take (s.length - 1 + 1)).prod, ↑s[s.length - 1]⟩ : Slice).length (s.take (s.length - 1 + 1)).prod) * (s.drop (s.length - 1 + 1)).prod := by
              simp
              rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength _ h_k]
              simpa [EqAddSub.of.Ge (show s.length ≥ 1 by omega)]
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
            let ⟨h_q_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
            have h_s_drop : s.drop (s.length - 1 + 1) = [] := by
              simp [EqAddSub.of.Ge (show s.length ≥ 1 by omega)]
            have h_r := r.isLt
            simp [h_s_drop] at h_q_div h_r
            have h_q := q.isLt
            simp at h_q
            rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength _ h_k] at h_q
            rw [List.Take_SubLength_1.eq.DropLast] at h_q
            simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
            rw [GetGetSlice.eq.Get.of.GtGet.GtLength]
            ·
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              rw [GetCast.eq.Get.of.Eq.fin (by simp)]
              simp
              have h_lt : k * (s.rotate (s.length - 1)).tail.prod + ↑t < (s.take (s.length - s.length)).prod * ((s.drop (s.length - s.length)).rotate (s.length ⊓ s.length - 1)).prod := by
                simp
                rw [ProdRotate.eq.Prod]
                rw [List.TailRotate.eq.DropLast.of.GtLength_0 (by omega)]
                apply LtAddMul.of.Lt.Lt_Div.Dvd
                .
                  apply DropLast.dvd.Prod
                .
                  rw [List.ProdDropLast.eq.DivProd.of.GtLength_0.Gt_0 (by grind) (by grind)]
                  rwa [Nat.EqDiv_Div.of.Ne_0.Dvd]
                  .
                    apply List.Get.dvd.Prod.of.GtLength
                  .
                    rw [List.Prod.eq.MulProdDropLast.of.GtLength_0 (by grind)]
                    apply Nat.Mul.ne.Zero.of.Ne_0.Ne_0
                    repeat grind
                .
                  grind
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
              have h_q' := q'.isLt
              simp at h_q'
              have h_r' := r'.isLt
              simp [List.ProdRotate.eq.Prod] at h_r'
              let ⟨_, h_r'_div⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              unfold Tensor.rotate
              simp
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                have h_r' : r' < ((s.drop (s.length - s.length)).drop ((s.length ⊓ s.length - 1) % (s.drop (s.length - s.length)).length)).prod * ((s.drop (s.length - s.length)).take ((s.length ⊓ s.length - 1) % (s.drop (s.length - s.length)).length)).prod := by
                  simpa [List.MulProdS.eq.Prod.comm]
                let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
                let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                rw [List.TailRotate.eq.DropLast.of.GtLength_0 (by grind)] at h_r'_div
                simp [ProdRotate.eq.Prod] at h_r'_div
                simp [List.Take_SubLength_1.eq.DropLast] at h_qₐ_div h_rₐ_mod
                simp [h_r'_div] at h_qₐ_div h_rₐ_mod
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                apply congrArg
                simp [h_q', h_r]
                simp [h_qₐ_div, h_rₐ_mod, h_q_div]
                simp [EqAddSub.of.Ge (show s.length ≥ 1 by omega)]
                rw [List.ProdDrop.eq.Get.of.GtLength_0 (by omega)]
                rw [List.Prod.eq.MulProdDropLast.of.GtLength_0 (by grind) (s := s)]
                simp [Nat.DivMod_Mul.eq.ModDiv]
                rw [Nat.EqDivAddMul.of.Lt (by grind)]
                repeat rw [EqMod.of.Lt (by grind)]
              ·
                simp
                rw [ProdRotate.eq.Prod]
                rw [MulProdS.eq.Prod.comm]
            ·
              simpa
          ·
            simp
            rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength _ h_k]
            rw [Drop.eq.Nil.of.LeLength (by grind)]
            simp
            rw [TailRotate.eq.DropLast.of.GtLength_0 (by omega)]
            rw [List.DropLast.eq.Take_SubLength_1]
      ·
        simp
        rwa [List.GetRotate.eq.Get.of.GtLength.Gt_0 (by omega) (by omega)]


-- created on 2026-04-08
-- updated on 2026-04-16
