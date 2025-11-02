import Lemma.Tensor.GetPermute.eq.PermuteGet.of.Lt_Get_0.GtLength_1
import Lemma.Nat.DivAddMul.eq.AddDiv.of.Gt_0
import Lemma.List.ProdTail.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.DropTail.eq.Drop
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.LtAddMul.of.Lt.Eq
import Lemma.Nat.LtAddMul.of.Lt.Lt.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.TailPermute.eq.PermuteTail.of.GtLength_Add_1
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute.eq.Get_0.of.GtVal_0
import sympy.tensor.tensor
open Tensor Bool List Vector Nat
set_option maxHeartbeats 400000


@[main]
private lemma main
  {s : List ℕ}
  {i k : ℕ}
-- given
  (h_i : i + 1 < s.length)
  (h_k : k < s[0])
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.permute ⟨i + 1, by omega⟩ d).get ⟨k, by rwa [LengthPermute.eq.Get_0.of.GtVal_0 (by simp)]⟩ ≃ (X.get ⟨k, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).permute ⟨i, by simp; omega⟩ d := by
-- proof
  by_cases h_d : d = 0
  .
    subst h_d
    simp
    sorry
  .
    by_cases h_i0 : i = 0
    .
      have : NeZero d := ⟨h_d⟩
      subst h_i0
      simp
      apply GetPermute.eq.PermuteGet.of.Lt_Get_0.GtLength_1 _ h_k
    .
      rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := d)]
      simp
      split_ifs with h_d0 h_pos?
      .
        apply SEq.of.SEqDataS.Eq
        .
          apply TailPermute.eq.PermuteTail.of.GtLength_Add_1 h_i
        .
          simp
          rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by simp; omega) (X.permute ⟨i + 1, h_i⟩ d) ⟨k, by rwa [GetPermute.eq.Get.of.Lt (by simp)]⟩]
          apply SEqCastS.of.SEq.Eq.Eq
          .
            simp
          .
            rw [MulProdS.eq.ProdAppend]
            rw [Permute.eq.Append_AppendRotateTakeDrop]
          .
            simp
            have h_prod : ((s.permute ⟨i + 1, h_i⟩ ↑d).drop 1).prod = (s.tail.take i).prod * (((s.tail.drop i).take (d + 1)).rotate 1 ++ (s.tail.drop i).drop (d + 1)).prod := by
              rw [MulProdS.eq.ProdAppend]
              apply congrArg
              have := Permute.eq.Append_AppendRotateTakeDrop (s := s.tail) (i := ⟨i, by grind⟩) (d := d)
              simp at this
              simp [← this]
              apply List.TailPermute.eq.PermuteTail.of.GtLength_Add_1 h_i
            apply SEq.of.All_EqGetS.Eq.fin h_prod
            intro t
            have h_t := LtVal t
            simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            have := h_t
            simp only [h_prod] at h_t
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
            let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
            have h_r := LtVal r
            simp only [ProdAppend.eq.MulProdS] at h_r
            simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
            unfold permuteHead
            simp [GetCast.eq.Get.of.Eq.fin]
            rw [@Tensor.Permute.eq.Ite (i := ⟨i + 1, by omega⟩) (d := d)]
            simp
            split_ifs with h_d0
            .
              omega
            .
              simp
              have h_lt : k * (s.permute ⟨i + 1, h_i⟩ ↑d).tail.prod + ↑t < (s.take (i + 1)).prod * (((s.drop (i + 1)).take (d + 1)).rotate 1 ++ (s.drop (i + 1)).drop (d + 1)).prod := by
                rw [MulProdS.eq.ProdAppend]
                have h_permute := Permute.eq.Append_AppendRotateTakeDrop (s := s) (i := ⟨i + 1, by grind⟩) (d := d)
                simp at h_permute
                simp [← h_permute]
                apply LtAddMul.of.Lt.Lt.Eq _ h_k
                .
                  simp at this
                  exact this
                .
                  rw [List.Prod.eq.Mul_ProdTail.of.GtLength_0]
                  .
                    rw [List.GetPermute.eq.Get.of.Lt]
                    simp
                  .
                    simp
                    omega
              rw [GetCast.eq.Get.of.Eq.Lt.fin h_lt]
              .
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                have h_r' := LtVal r'
                simp only [ProdAppend.eq.MulProdS] at h_r'
                let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
                let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                have h_qₐ := LtVal qₐ
                simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₐ
                repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                unfold Tensor.permuteHead Tensor.rotate
                simp
                repeat rw [GetCast.eq.Get.of.Eq.Lt.fin (by assumption)]
                .
                  let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
                  let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                  have h_qₑ := LtVal qₑ
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₑ
                  let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₐ
                  let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                  repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                  rw [GetTranspose.eq.Get.fin]
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, by grind⟩) (by omega)]
                  simp
                  repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
                  .
                    let ⟨qᵢ, rᵢ, h_qᵢrᵢ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₑ
                    let ⟨h_qᵢ_div, h_rᵢ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qᵢrᵢ
                    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qᵢrᵢ]
                    rw [GetTranspose.eq.Get.fin]
                    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    apply congrArg
                    simp
                    conv_rhs =>
                      rw [Add_Add.eq.AddAdd]
                      arg 1
                      rw [Add.comm]
                    rw [AddAdd.eq.Add_Add (a := q * (s.drop (i + 1)).prod)]
                    simp only [List.DropTail.eq.Drop] at h_q_div h_r_mod
                    simp only [← List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (show (s.drop (i + 1)).length > 0 by simp; omega)] at h_q_div h_q'_div h_r_mod h_r'_mod
                    rw [List.ProdPermute.eq.Prod] at h_q_div h_q'_div h_r_mod h_r'_mod
                    rw [List.TailPermute.eq.PermuteTail.of.GtLength_Add_1 (by simp; omega)] at h_q'_div h_r'_mod
                    rw [List.ProdPermute.eq.Prod] at h_q'_div h_r'_mod
                    rw [ProdTail.eq.MulProdS (d := i), Mul_Mul.eq.MulMul] at h_q'_div h_r'_mod
                    rw [ProdRotate.eq.Prod, MulProdS.eq.ProdAppend] at h_r'
                    simp at h_r'
                    rw [Nat.DivAddMul.eq.AddDiv.of.Gt_0 (by omega)] at h_q'_div
                    simp [h_q'_div, h_q_div]
                    rw [MulAdd.eq.AddMulS]
                    simp [AddAdd.eq.Add_Add]
                    rw [MulMul.eq.Mul_Mul]
                    simp [← ProdTail.eq.MulProdS]
                    simp at h_rₑ_mod h_rₐ_mod h_r'_mod h_r_mod h_qₕ_div h_rₕ_mod h_qᵢ_div h_rᵢ_mod h_qₐ_div h_qₑ_div
                    have h_rₐₑ_eq : rₐ.val = rₑ.val := by grind
                    have h_qₕᵢ_eq : qₕ.val = qᵢ.val := by grind
                    have h_rₕᵢ_eq : rₕ.val = rᵢ.val := by grind
                    simp [h_rₐₑ_eq, h_qₕᵢ_eq, h_rₕᵢ_eq]
                  .
                    apply LtAddMul.of.Lt.Eq
                    .
                      simp
                      apply ProdTail.eq.MulProdS
                    .
                      rw [List.ProdDrop.eq.MulProdS s (i + 1) (d + 1)]
                      apply AddMul.lt.Mul.of.Lt.Lt
                      .
                        apply LtAddMul.of.Lt.Eq
                        .
                          simp
                        .
                          have h_qₕ := LtVal qₕ
                          simp at h_qₕ
                          exact h_qₕ
                      .
                        have h_rₐ := LtVal rₐ
                        simp at h_rₐ
                        exact h_rₐ
                  .
                    simp
                  .
                    exact h_qₑ
                  .
                    rw [MulProdS.eq.ProdAppend]
                    rw [Rotate.eq.AppendDrop__Take]
                .
                  rw [MulProdS.eq.ProdAppend]
                  rw [Rotate.eq.AppendDrop__Take]
                .
                  rw [MulProdS.eq.ProdAppend]
              .
                rw [MulProdS.eq.ProdAppend]
                rw [Permute.eq.Append_AppendRotateTakeDrop]
      .
        omega
      .
        omega


-- created on 2025-11-02
