import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.GetPermute.eq.Get.of.Gt
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailPermute.eq.PermuteTail.of.GtLength_Add_1
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtAddMul.of.Lt.Lt.Eq
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute.eq.Get_0.of.GtVal_0
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector Fin


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
  {k : ℕ}
-- given
  (h : s.length > 1)
  (h_k : k < s[0])
  (X : Tensor α s) :
-- imply
  (X.permute ⟨1, by omega⟩ d).get ⟨k, by rwa [LengthPermute.eq.Get_0.of.GtVal_0 (by simp)]⟩ ≃ (X.get ⟨k, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).permute ⟨0, by simp; omega⟩ d := by
-- proof
  rw [@Tensor.Permute.eq.Ite (i := ⟨0, by simp; omega⟩) (d := d)]
  simp
  have h_d := NeZero.pos d
  split_ifs with h_d0
  ·
    omega
  ·
    apply SEq_Cast.of.SEq.Eq
    ·
      rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
    ·
      unfold permuteHead
      simp
      apply SEq.of.SEqDataS.Eq
      ·
        rw [TailPermute.eq.PermuteTail.of.GtLength_Add_1 h]
        rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
      ·
        simp
        rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by simp; omega) (X.permute ⟨1, h⟩ d) ⟨k, by rwa [GetPermute.eq.Get.of.Gt (by simp)]⟩]
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          rw [MulProdS.eq.ProdAppend]
        ·
          simp
          have h_prod : ((s.permute ⟨1, h⟩ ↑d).drop 1).prod = ((s.tail.take (d + 1)).rotate 1).prod * (s.tail.drop (d + 1)).prod := by
            simp [TailPermute.eq.PermuteTail.of.GtLength_Add_1 h]
            simp [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
          apply SEq.of.All_EqGetS.Eq.fin h_prod
          intro t
          have h_t := t.isLt
          simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          have := h_t
          simp only [h_prod] at h_t
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
          have h_q := q.isLt
          simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q
          let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
          have h_r := r.isLt
          simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
          rw [@Tensor.Permute.eq.Ite (i := ⟨1, by omega⟩) (d := d)]
          simp
          split_ifs with h_d0
          ·
            omega
          ·
            simp
            have h_lt : k * (s.permute ⟨1, h⟩ d).tail.prod + t < (s.take 1).prod * (((s.drop 1).take (d + 1)).rotate 1 ++ (s.drop 1).drop (d + 1)).prod := by
              rw [MulProdS.eq.ProdAppend]
              have h_permute := Permute.eq.Append_AppendRotateTakeDrop (s := s) (i := ⟨1, by grind⟩) (d := d)
              simp at h_permute
              simp [← h_permute]
              apply LtAddMul.of.Lt.Lt.Eq _ h_k
              ·
                simp at this
                exact this
              ·
                rw [Prod.eq.Mul_ProdTail.of.GtLength_0]
                ·
                  rw [GetPermute.eq.Get.of.Gt]
                  simp
                ·
                  simp
                  omega
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
              let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              have h_r' := r'.isLt
              simp only [ProdAppend.eq.MulProdS] at h_r'
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              unfold Tensor.permuteHead Tensor.rotate
              simp [GetCast.eq.Get.of.Eq.fin]
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
                let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                have h_qₑ := qₑ.isLt
                simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₑ
                let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_q
                let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, by grind⟩) (by omega)]
                simp
                repeat rw [GetCast.eq.Get.of.Eq.fin]
                ·
                  let ⟨qᵢ, rᵢ, h_qᵢrᵢ⟩ := Any_Eq_AddMul.of.Lt_Mul h_qₑ
                  let ⟨h_qᵢ_div, h_rᵢ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qᵢrᵢ
                  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qᵢrᵢ]
                  rw [GetTranspose.eq.Get.fin]
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  apply congrArg
                  simp
                  rw [TailPermute.eq.PermuteTail.of.GtLength_Add_1 (by omega)] at h_q'_div h_r'_mod
                  simp only [ProdAppend.eq.MulProdS] at h_q'_div h_r'_mod
                  simp only [ProdRotate.eq.Prod, MulProdS.eq.Prod] at h_q'_div h_r' h_r'_mod
                  simp [ProdPermute.eq.Prod] at h_q'_div h_r'_mod
                  simp at h_r'
                  rw [DivAddMul.eq.Add_Div.of.Gt_0 (by omega)] at h_q'_div
                  rw [ProdRotate.eq.Prod, MulProdS.eq.Prod] at h_t
                  simp [Div.eq.Zero.of.Lt h_t] at h_q'_div
                  simp [EqMod.of.Lt h_t] at h_r'_mod
                  simp at h_rₑ_mod h_r_mod h_q_div h_qₑ_div h_rₕ_mod h_rᵢ_mod h_qᵢ_div
                  have h_r_eq : rₑ = r.val := by grind
                  have h_rₕᵢ_eq : rₕ.val = rᵢ.val := by grind
                  have h_qₕᵢ_eq : qₕ.val = qᵢ.val := by grind
                  simp [h_q'_div, h_r_eq, h_rₕᵢ_eq, h_qₕᵢ_eq]
                ·
                  simp
                ·
                  rw [MulProdS.eq.ProdAppend]
                  rw [Rotate.eq.AppendDrop__Take]
              ·
                rw [MulProdS.eq.ProdAppend]
                rw [Rotate.eq.AppendDrop__Take]
            ·
              rw [MulProdS.eq.ProdAppend]
              rw [Permute.eq.Append_AppendRotateTakeDrop]


-- created on 2025-11-02
