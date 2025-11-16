import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.DropTail.eq.Drop
import Lemma.List.GetPermute.eq.Get.of.Lt
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTail.eq.MulProdS
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailPermute.eq.PermuteTail.of.GtLength_Add_1
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.DivAddMul.eq.AddDiv.of.Gt_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtAddMul.of.Lt.Eq
import Lemma.Nat.LtAddMul.of.Lt.Lt.Eq
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.GetPermute.eq.PermuteGet.of.Lt_Get_0.GtLength_1
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute.eq.Get_0.of.GtVal_0
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqGetS.of.SEq.Lt_Length
import Lemma.Tensor.SEqPermute__0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Bool List Nat Tensor Vector
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
  have h_Xk : k < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.permute ⟨i + 1, by omega⟩ d).get ⟨k, by rwa [LengthPermute.eq.Get_0.of.GtVal_0 (by simp)]⟩ ≃ (X.get ⟨k, h_Xk⟩).permute ⟨i, by simp; omega⟩ d := by
-- proof
  intro h_Xk
  if h_d : d = 0 then
    subst h_d
    simp
    have := SEqPermute__0 (X.get ⟨k, h_Xk⟩) ⟨i, by grind⟩
    apply SEq.symm ∘ SEq.trans this
    apply SEqGetS.of.SEq.Lt_Length
    apply SEq_Permute__0
  else if h_i0 : i = 0 then
    have : NeZero d := ⟨h_d⟩
    subst h_i0
    simp
    apply GetPermute.eq.PermuteGet.of.Lt_Get_0.GtLength_1 _ h_k
  else
    rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := d)]
    simp
    split_ifs with h_d0 h_pos
    ·
      apply SEq.of.SEqDataS.Eq
      ·
        apply TailPermute.eq.PermuteTail.of.GtLength_Add_1 h_i
      ·
        simp
        rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by simp; omega) (X.permute ⟨i + 1, h_i⟩ d) ⟨k, by rwa [GetPermute.eq.Get.of.Lt (by simp)]⟩]
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [Permute.eq.Append_AppendRotateTakeDrop]
        ·
          simp
          have h_prod : ((s.permute ⟨i + 1, h_i⟩ ↑d).drop 1).prod = (s.tail.take i).prod * (((s.tail.drop i).take (d + 1)).rotate 1 ++ (s.tail.drop i).drop (d + 1)).prod := by
            rw [MulProdS.eq.ProdAppend]
            apply congrArg
            have := Permute.eq.Append_AppendRotateTakeDrop (s := s.tail) (i := ⟨i, by grind⟩) (d := d)
            simp at this
            simp [← this]
            apply TailPermute.eq.PermuteTail.of.GtLength_Add_1 h_i
          apply SEq.of.All_EqGetS.Eq.fin h_prod
          intro t
          have h_t := t.isLt
          simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          have := h_t
          simp only [h_prod] at h_t
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
          have h_r := r.isLt
          simp only [ProdAppend.eq.MulProdS] at h_r
          simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
          unfold permuteHead
          simp [GetCast.eq.Get.of.Eq.fin]
          rw [@Tensor.Permute.eq.Ite (i := ⟨i + 1, by omega⟩) (d := d)]
          simp
          split_ifs with h_d0
          ·
            omega
          ·
            simp
            have h_lt : k * (s.permute ⟨i + 1, h_i⟩ ↑d).tail.prod + ↑t < (s.take (i + 1)).prod * (((s.drop (i + 1)).take (d + 1)).rotate 1 ++ (s.drop (i + 1)).drop (d + 1)).prod := by
              rw [MulProdS.eq.ProdAppend]
              have h_permute := Permute.eq.Append_AppendRotateTakeDrop (s := s) (i := ⟨i + 1, by grind⟩) (d := d)
              simp at h_permute
              simp [← h_permute]
              apply LtAddMul.of.Lt.Lt.Eq _ h_k
              ·
                simp at this
                exact this
              ·
                rw [Prod.eq.Mul_ProdTail.of.GtLength_0]
                ·
                  rw [GetPermute.eq.Get.of.Lt]
                  simp
                ·
                  simp
                  omega
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              obtain ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              have h_r' := r'.isLt
              simp only [ProdAppend.eq.MulProdS] at h_r'
              let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
              let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
              have h_qₐ := qₐ.isLt
              simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₐ
              repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
              unfold Tensor.permuteHead Tensor.rotate
              simp
              repeat rw [GetCast.eq.Get.of.Eq.fin]
              ·
                let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
                let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                have h_qₑ := qₑ.isLt
                simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₑ
                let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₐ
                let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, by grind⟩) (by omega)]
                simp
                repeat rw [GetCast.eq.Get.of.Eq.fin]
                ·
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
                  simp only [DropTail.eq.Drop] at h_q_div h_r_mod
                  simp only [← Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (show (s.drop (i + 1)).length > 0 by simp; omega)] at h_q_div h_q'_div h_r_mod h_r'_mod
                  rw [ProdPermute.eq.Prod] at h_q_div h_q'_div h_r_mod h_r'_mod
                  rw [TailPermute.eq.PermuteTail.of.GtLength_Add_1 (by simp; omega)] at h_q'_div h_r'_mod
                  rw [ProdPermute.eq.Prod] at h_q'_div h_r'_mod
                  rw [ProdTail.eq.MulProdS (d := i), Mul_Mul.eq.MulMul] at h_q'_div h_r'_mod
                  rw [ProdRotate.eq.Prod, MulProdS.eq.ProdAppend] at h_r'
                  simp at h_r'
                  rw [DivAddMul.eq.AddDiv.of.Gt_0 (by omega)] at h_q'_div
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
            ·
              rw [MulProdS.eq.ProdAppend]
              rw [Permute.eq.Append_AppendRotateTakeDrop]
    repeat omega


-- created on 2025-11-02
