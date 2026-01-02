import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.EqPermute__0
import Lemma.List.EqTake.of.LeLength
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute.eq.Ite
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add_1.ge.Mod1
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Eq.of.Sub.eq.Zero.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.SubSub
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqPermuteHeadS.of.LeLength
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Tensor.SEqPermuteTail_1
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Tensor Bool List Vector Fin
set_option maxHeartbeats 400000


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i + d ≥ s.length - 1)
  (X : Tensor α s) :
-- imply
  X.permute i d ≃ X.permute i (s.length - 1 - i : ℕ) := by
-- proof
  if h_d : i + d = s.length - 1 then
    have h_d := Eq_Sub.of.EqAdd.left h_d
    subst h_d
    rfl
  else
    have h_d := Gt.of.Ge.Ne h h_d
    rw [@Tensor.Permute.eq.Ite]
    simp
    split_ifs with h_d0 h_pos? h_i h_length
    ·
      omega
    ·
      have h_s : 0 < s.length := by omega
      have h_i : i = ⟨0, h_s⟩ := by aesop
      subst h_i
      simp_all
      apply SEqCast.of.SEq.Eq
      ·
        simp [Permute.eq.AppendRotateTake___Drop.of.EqVal_0]
      ·
        rw [@Tensor.Permute.eq.Ite]
        simp
        split_ifs with h_s h_s_length h_0
        ·
          have h_s : s.length = 1 := by omega
          apply SEq_Cast.of.SEq.Eq
          ·
            simp [h_s]
            rw [EqPermute__0]
          ·
            have := SEqPermuteHeadS.of.LeLength (s := s) (n := d + 1) (by omega) X
            rw [h_s] at this
            apply this.trans
            apply SEqPermuteHead_1
        ·
          apply SEq_Cast.of.SEq.Eq
          ·
            simp [Permute.eq.AppendRotateTake___Drop.of.EqVal_0]
          ·
            rw [EqAddSub.of.Ge (by omega)]
            apply SEqPermuteHeadS.of.LeLength (s := s) (n := d + 1) (by omega) X
        ·
          have h_s := Eq.of.Sub.eq.Zero.Ge (by omega) h_0.symm
          apply SEq_Cast.of.SEq.Eq
          ·
            simp [h_s]
            rw [EqPermute__0]
          ·
            have := SEqPermuteHeadS.of.LeLength (s := s) (n := d + 1) (by omega) X
            rw [h_s] at this
            apply this.trans
            have := SEqPermuteHead_1 X
            apply this.trans
            rw [show (1 - (s.length - 1 : ℕ) : ℤ).toNat = 1 by omega]
            have := SEqPermuteTail_1 X
            symm
            apply this.trans
            rfl
        ·
          grind
    ·
      apply SEq.of.SEqDataS.Eq
      ·
        rw [EqPermuteS.of.Add.ge.SubLength_1 (by omega)]
      ·
        simp
        apply SEqCast.of.SEq.Eq
        ·
          rw [MulProdS.eq.ProdAppend]
          apply congrArg
          rw [Permute.eq.Append_AppendRotateTakeDrop]
        ·
          rw [@Tensor.Permute.eq.Ite]
          simp
          split_ifs with h_s h_s_length h_i0
          ·
            rw [DataCast.eq.Cast_Data.of.Eq]
            ·
              apply SEq_Cast.of.SEq.Eq
              ·
                simp [h_s]
                rw [EqPermute__0]
              ·
                apply SEq.of.All_EqGetS.Eq
                ·
                  intro t
                  have h_t := t.isLt
                  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
                  let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
                  have h_r := r.isLt
                  simp only [ProdAppend.eq.MulProdS] at h_r
                  simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
                  unfold Tensor.permuteHead
                  simp [GetElem.getElem]
                  rw [GetCast.eq.Get.of.Eq.fin]
                  ·
                    let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r
                    let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                    have h_qₐ := qₐ.isLt
                    have h_rₐ := rₐ.isLt
                    simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₐ
                    simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
                    unfold Tensor.rotate
                    simp
                    rw [GetCast.eq.Get.of.Eq.fin]
                    ·
                      let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_qₐ
                      let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                      rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
                      rw [GetTranspose.eq.Get.fin]
                      repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                      apply congrArg
                      simp [h_qr]
                      simp [Drop.eq.Nil.of.LeLength (show i + (d + 1) ≥ s.length by omega)] at h_rₐ h_qₐ_div ⊢
                      simp [h_rₐ]
                      simp [ProdRotate.eq.Prod]
                      simp [EqTake.of.LeLength (show (d + 1) ≥ (s.drop i).length by simp; omega)]
                      simp [h_qₕ_div, h_rₕ_mod]
                      rw [EqMin.of.Ge (by omega)]
                      rw [TakeTake.eq.Take.of.Ge (Add_1.ge.Mod1 d (s.length - i))]
                      simp [h_qₐ_div]
                      rw [ProdRotate.eq.Prod] at h_r
                      rw [MulProdS.eq.ProdAppend] at h_r
                      simp at h_r
                      rw [SubSub.comm] at h_s
                      have h_i := Eq.of.Sub.eq.Zero.Ge (by omega) h_s
                      simp [h_i]
                      left
                      apply EqMod_1'0
                    ·
                      rw [MulProdS.eq.ProdAppend]
                      rw [Rotate.eq.AppendDrop__Take]
                  ·
                    rw [MulProdS.eq.ProdAppend]
                ·
                  rw [MulProdS.eq.ProdAppend]
                  rw [← Permute.eq.Append_AppendRotateTakeDrop]
                  rw [ProdPermute.eq.Prod]
            ·
              simp [h_s]
              rw [EqPermute__0]
          ·
            simp
            apply SEq_Cast.of.SEq.Eq
            ·
              rw [MulProdS.eq.ProdAppend]
              rw [Permute.eq.Append_AppendRotateTakeDrop]
            ·
              rw [show (s.length - 1 - i + 1) = s.length - i by omega]
              apply SEq.of.All_EqGetS.Eq
              ·
                intro t
                have h_t := t.isLt
                let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
                let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
                have h_r := r.isLt
                simp only [ProdAppend.eq.MulProdS] at h_r
                simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
                unfold Tensor.permuteHead
                simp
                have h_take : (s.drop i).take (d + 1) = (s.drop i).take (s.length - i) := by
                  repeat rw [EqTake.of.LeLength]
                  repeat simp
                  omega
                have h_drop : (s.drop i).drop (d + 1) = (s.drop i).drop (s.length - i) := by
                  simp
                  repeat rw [Drop.eq.Nil.of.LeLength]
                  repeat omega
                simp only [h_take, h_drop] at h_t
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                simp [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
                have h_r' := r'.isLt
                simp only [ProdAppend.eq.MulProdS] at h_r'
                simp [GetElem.getElem]
                repeat rw [GetCast.eq.Get.of.Eq.fin]
                ·
                  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r
                  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                  have h_qₐ := qₐ.isLt
                  have h_rₐ := rₐ.isLt
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₐ
                  simp [Drop.eq.Nil.of.LeLength (show i + (d + 1) ≥ s.length by omega)] at h_q_div h_r_mod h_rₐ h_qₐ_div
                  simp [EqTake.of.LeLength (show d + 1 ≥ (s.drop i).length by simp; omega)] at h_q_div h_r_mod
                  simp [EqTake.of.LeLength (show (s.length - i) ≥ (s.drop i).length by simp)] at h_q'_div h_r'_mod
                  simp [ProdRotate.eq.Prod] at h_q_div h_r_mod h_q'_div h_r'_mod
                  have h_q_eq : q = q' := by grind
                  have h_r_eq : r.val = r'.val := by grind
                  let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
                  let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                  have h_qₑ := qₑ.isLt
                  have h_rₑ := rₑ.isLt
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₑ
                  simp at h_rₑ h_qₑ_div
                  have h_qₐₑ_eq : qₐ.val = qₑ.val := by grind
                  repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                  unfold Tensor.rotate
                  repeat rw [GetCast.eq.Get.of.Eq.fin]
                  ·
                    let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_qₐ
                    let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                    let ⟨qᵢ, rᵢ, h_qᵢrᵢ⟩ := Any_Eq_AddMul.of.Lt_Mul h_qₑ
                    let ⟨h_qᵢ_div, h_rᵢ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qᵢrᵢ
                    have h_qₕᵢ_eq : qₕ.val = qᵢ.val := by grind
                    have h_rₕᵢ_eq : rₕ.val = rᵢ.val := by grind
                    repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                    repeat rw [GetTranspose.eq.Get.fin]
                    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    apply congrArg
                    simp [h_q_eq, h_rₐ, h_rₑ]
                    rw [EqMin.of.Ge (by omega)]
                    simp [TakeDrop.eq.DropTake]
                    simp [EqTake.of.LeLength (show (i + (d + 1)) ≥ s.length by omega)]
                    simp [Drop.eq.Nil.of.LeLength (show i + (d + 1) ≥ s.length by omega)]
                    simp [h_qₕᵢ_eq, h_rₕᵢ_eq]
                  ·
                    rw [MulProdS.eq.ProdAppend]
                  .
                    rw [Rotate.eq.AppendDrop__Take]
                  ·
                    rw [MulProdS.eq.ProdAppend]
                  .
                    rw [Rotate.eq.AppendDrop__Take]
                repeat rw [MulProdS.eq.ProdAppend]
              ·
                repeat rw [MulProdS.eq.ProdAppend]
                repeat rw [← Permute.eq.Append_AppendRotateTakeDrop]
                have := Permute.eq.Append_AppendRotateTakeDrop (s := s) (i := i) (d := s.length - 1 - i)
                simp [show (s.length - 1 - i + 1) = s.length - i by omega] at this
                simp [← this]
                repeat rw [ProdPermute.eq.Prod]
          repeat grind
    repeat omega


-- created on 2025-10-29
-- updated on 2025-10-30
