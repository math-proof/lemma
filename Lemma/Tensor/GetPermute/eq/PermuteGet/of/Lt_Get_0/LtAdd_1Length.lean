import Lemma.Vector.GetTranspose.eq.Get
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
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
  rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := d)]
  simp
  split_ifs with h_d0 h_pos? h_i0 h_i
  .
    subst h_d0
    simp
    sorry
  .
    subst h_i0
    simp at h_i ⊢
    sorry
  .
    apply SEq.of.SEqDataS.Eq
    .
      sorry
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
        apply Vector.SEq.of.All_EqGetS.Eq.fin h_prod
        intro t
        have h_t := Nat.LtVal t
        simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        have := h_t
        simp only [h_prod] at h_t
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
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
            apply LtAddMul.of.Lt.Lt.Eq (m := s[0]) _ h_k
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
            have h_r' := LtVal r'
            simp only [ProdAppend.eq.MulProdS] at h_r'
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
            have h_qₐ := LtVal qₐ
            simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₐ
            repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
            unfold Tensor.permuteHead Tensor.rotate
            simp
            repeat rw [GetCast.eq.Get.of.Eq.Lt.fin (by assumption)]
            .
              let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
              have h_qₑ := LtVal qₑ
              simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₑ
              let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₐ
              repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
              rw [GetTranspose.eq.Get.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              rw [Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, by grind⟩) (by omega)]
              simp
              repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
              .
                let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₑ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                apply congrArg
                simp
                sorry
              .
                simp
                sorry
              .
                sorry
              .
                sorry
              .
                sorry
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
