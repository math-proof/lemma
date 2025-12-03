import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.DropTail.eq.Drop
import Lemma.List.GetPermute__Neg.eq.Get_0.of.Gt
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDropTake.eq.MulProdDropTake.of.Gt.GtLength
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTail.eq.MulProdTakeTail
import Lemma.List.ProdTail.eq.MulProdTakeTailTake.of.Ge
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.Tail.eq.Drop_1
import Lemma.List.TailPermute__Neg.eq.PermuteTail.of.Gt
import Lemma.List.TailTake.eq.TakeTail
import Lemma.List.TakeDropTake.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Ne_0
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.SubAddS.eq.Sub
import Lemma.Nat.ToNatSub_Neg.eq.Add_1
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetPermuteTail.as.PermuteTailGet.of.Lt_Get_0.GtLength
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute__Neg.eq.Get_0.of.Gt
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqPermute__0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector
set_option maxHeartbeats 1000000


@[main]
private lemma main
  {s : List ℕ}
  {i k d : ℕ}
-- given
  (h_i : i + 1 < s.length)
  (h_k : k < s[0])
  (h_d : i ≥ d)
  (X : Tensor α s) :
-- imply
  have h_Xk : k < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.permute ⟨i + 1, h_i⟩ (-d)).get ⟨k, by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]⟩ ≃ (X.get ⟨k, h_Xk⟩).permute ⟨i, by simp; omega⟩ (-d) := by
-- proof
  intro h_Xk
  have h_toNat := ToNatSub_Neg.eq.Add_1 d
  if h_d0 : d = 0 then
    subst h_d0
    simp
    have := SEqPermute__0 (X.get ⟨k, h_Xk⟩) ⟨i, by grind⟩
    apply SEq.symm ∘ SEq.trans this
    apply SEqGetS.of.SEq.GtLength
    apply SEq_Permute__0
  else if h_i0 : i = s.length - 2 then
    have : NeZero d := ⟨h_d0⟩
    -- subst h_i0
    rw [@Tensor.Permute.eq.Ite (i := ⟨i, by grind⟩) (d := -d)]
    simp
    split_ifs with h_d0 h_pos h_pos
    ·
      omega
    ·
      omega
    ·
      apply SEq_Cast.of.SEq.Eq
      ·
        simp only [h_toNat]
        rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (by simp; omega)]
      ·
        rw [h_toNat]
        have := Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1 (by simp; omega) X (i := ⟨i + 1, h_i⟩) (d := d)
        have := SEqGetS.of.SEq.GtLength.fin (by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by grind)]) this (i := k)
        apply SEq.trans this
        apply GetPermuteTail.as.PermuteTailGet.of.Lt_Get_0.GtLength _ h_k
        omega
    ·
      omega
  else
    rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := -d)]
    simp
    split_ifs with h_d0? h_i0 h_i_end
    repeat omega
    have := Permute.eq.Ite X ⟨i + 1, by grind⟩ (-d : ℤ)
    have h_i_ne : i + 1 ≠ s.length - 1 := by omega
    simp [h_d0, h_d0?, h_i_ne] at this
    have h_k' : k < (s.permute ⟨i + 1, by grind⟩ (-↑d))[0]'(by simp; grind) := by 
      rwa [GetPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]
    simp [EqGetS.of.Eq.GtLength_0 (by simp; omega) this ⟨k, h_k'⟩]
    apply SEq.of.SEqDataS.Eq
    ·
      rw [TailPermute__Neg.eq.PermuteTail.of.Gt (by simp; omega)]
      simp
    ·
      simp
      rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, h_k'⟩)]
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        simp only [h_toNat]
        simp [Permute__Neg.eq.Append_AppendRotateDropTake]
        simp [Mul_Mul.eq.MulMul]
        repeat rw [EqMin.of.Le (by omega)]
        simp
      ·
        simp
        apply SEq.of.All_EqGetS.Eq.fin
        ·
          intro t
          have h_t := t.isLt
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp [TailPermute__Neg.eq.PermuteTail.of.Gt (show (⟨i + 1, h_i⟩ : Fin s.length) > d by simp; omega)]
            simp at h_t
            rw [TailPermute__Neg.eq.PermuteTail.of.Gt (by simp; omega)] at h_t
            simp only [Permute__Neg.eq.Append_AppendRotateDropTake, ProdAppend.eq.MulProdS] at h_t
            simp at h_t
            rw [EqMin.of.Le (by omega)] at h_t
            have h_lt : t < ((s.tail.take (i + 1)).take ((s.tail.take (i + 1)).length - (1 - (-d : ℤ)).toNat) ++ ((s.tail.take (i + 1)).drop ((s.tail.take (i + 1)).length - (1 - (-d : ℤ)).toNat)).rotate ((1 - (-d : ℤ)).toNat ⊓ (s.tail.take (i + 1)).length - 1)).prod * (s.tail.drop (i + 1)).prod := by 
              simp only [h_toNat]
              simp
              repeat rw [EqMin.of.Le (by omega)]
              repeat rw [SubAddS.eq.Sub]
              simpa
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
            have h_q := q.isLt
            have h_r := r.isLt
            let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
            rw [TakeTake.eq.Take.of.Ge (by omega)] at h_t
            have h_lt : k * (s.tail.permute ⟨i, by grind⟩ ((-d : ℤ))).prod + ↑t < ((s.take (i + 1 + 1)).take ((s.take (i + 1 + 1)).length - (1 - (-d : ℤ)).toNat) ++ ((s.take (i + 1 + 1)).drop ((s.take (i + 1 + 1)).length - (1 - (-d : ℤ)).toNat)).rotate ((1 - (-d : ℤ)).toNat ⊓ (s.take (i + 1 + 1)).length - 1)).prod * (s.drop (i + 1 + 1)).prod := by 
              simp only [h_toNat]
              simp
              repeat rw [EqMin.of.Le (by omega)]
              repeat rw [SubAddS.eq.Sub]
              simp
              rw [TakeTake.eq.Take.of.Ge (by omega)]
              rw [show (i + 1 - d) = 1 + (i - d) by omega]
              rw [Drop_Add.eq.DropDrop (i := 1)]
              simp only [Drop_1.eq.Tail]
              rw [TailTake.eq.TakeTail]
              simp [Permute__Neg.eq.Append_AppendRotateDropTake]
              rw [EqMin.of.Le (by omega)]
              rw [TakeTake.eq.Take.of.Ge (by omega)]
              rw [MulMul.eq.Mul_Mul]
              rw [← TailTake.eq.TakeTail]
              rw [Add.comm (a := 1)]
              rw [Prod.eq.Mul_ProdTail.of.GtLength_0 (s := (s.take (i - d + 1))) (by simp; omega)]
              rw [MulMul.eq.Mul_Mul]
              apply AddMul.lt.Mul.of.Lt.Lt
              ·
                rwa [GetTake.eq.Get.of.Lt_LengthTake (by simp; omega)]
              ·
                rw [TailTake.eq.TakeTail]
                rwa [Mul_Mul.eq.MulMul]
            let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
            have h_q' := q'.isLt
            have h_r' := r'.isLt
            simp only [ProdAppend.eq.MulProdS] at h_q h_q'
            let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
            repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
            unfold Tensor.permuteTail
            simp
            repeat rw [GetCast.eq.Get.of.Eq.fin]
            ·
              let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_q
              have h_qₐ := qₐ.isLt
              have h_rₐ := rₐ.isLt
              let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
              let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_q'
              have h_qₑ := qₑ.isLt
              have h_rₑ := rₑ.isLt
              simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_rₐ h_rₑ
              let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
              repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
              simp
              unfold Tensor.rotate
              simp
              repeat rw [GetCast.eq.Get.of.Eq.fin]
              ·
                let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_rₐ
                have h_qₕ := qₕ.isLt
                have h_rₕ := rₕ.isLt
                let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                let ⟨qᵢ, rᵢ, h_qᵢrᵢ⟩ := Any_Eq_AddMul.of.Lt_Mul h_rₑ
                have h_qᵢ := qᵢ.isLt
                have h_rᵢ := rᵢ.isLt
                let ⟨h_qᵢ_div, h_rᵢ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qᵢrᵢ
                repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                repeat rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by grind) X (i := ⟨k, h_k⟩)]
                rw [GetCast.eq.Get.of.Eq.fin (by simp)]
                rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                apply congrArg
                simp only [h_toNat] at ⊢ h_qₐ_div h_rₐ_mod h_qₑ_div h_rₑ_mod h_qₕ_div h_rₕ_mod h_qᵢ_div h_rᵢ_mod h_qₐ h_rₐ h_qₑ h_rₑ h_qₕ h_rₕ h_qᵢ h_rᵢ h_q' h_q
                simp at ⊢ h_qₐ_div h_rₐ_mod h_qₑ_div h_rₑ_mod h_qₕ_div h_rₕ_mod h_qᵢ_div h_rᵢ_mod h_qₐ h_rₐ h_qₑ h_rₑ h_qₕ h_rₕ h_qᵢ h_rᵢ h_q' h_q
                simp [show (i + 1 + 1) ⊓ s.length = i + 1 + 1 by omega] at ⊢ h_qₑ_div h_rₑ_mod h_qᵢ_div h_rᵢ_mod h_qₑ h_rₑ h_qᵢ h_rᵢ h_q'
                simp [show (d ⊓ (i + 1)) = d by omega] at ⊢ h_qₑ_div h_rₑ_mod h_qᵢ_div h_rᵢ_mod h_qₑ h_rₑ h_qᵢ h_rᵢ h_q'
                simp [show (i + 1 + 1 - (i + 1 - d)) = d + 1 by omega] at ⊢ h_qᵢ_div h_rᵢ_mod h_qᵢ h_rᵢ
                simp [show (i + 1 - d + d) = i + 1 by omega]
                simp [show (i + 1) ⊓ (s.length - 1) = i + 1 by omega] at ⊢ h_qₐ_div h_rₐ_mod h_qₕ_div h_rₕ_mod h_qₐ h_rₐ h_qₕ h_rₕ h_q
                simp [show (i + 1 - (i - d)) = d + 1 by omega] at ⊢ h_qₕ_div h_rₕ_mod h_qₕ h_rₕ
                simp [show (d ⊓ i) = d by omega] at ⊢ h_qₐ_div h_rₐ_mod h_qₕ_div h_rₕ_mod h_qₐ h_rₐ h_qₕ h_rₕ h_q
                simp [show (i - d + d) = i by omega]
                simp [Permute__Neg.eq.Append_AppendRotateDropTake] at h_q'_div h_r'_mod
                simp [Mul_Mul.eq.MulMul] at h_q'_div h_r'_mod
                rw [DivAddMul.eq.Add_Div.of.Ne_0 (by omega)] at h_q'_div
                simp only [ProdRotate.eq.Prod] at h_qₐ_div h_rₐ_mod h_qₑ_div h_rₑ_mod h_q'_div h_q' h_q
                simp [h_q'_div] at h_qₑ_div h_rₑ_mod
                rw [MulMul.eq.Mul_Mul] at h_qₑ_div h_rₑ_mod
                simp [h_qₑ_div]
                simp [← TailTake.eq.TakeTail] at ⊢ h_qₐ_div h_rₐ_mod h_qₕ_div h_rₕ_mod h_rₑ_mod
                rw [ProdTail.eq.MulProdTakeTail (s.take (i + 1 + 1)) (i - d)]
                rw [Mul_Mul.eq.MulMul]
                simp [show (i - d + 1) = i + 1 - d by omega]
                rw [DivAddMul.eq.Add_Div.of.Ne_0 (by grind)]
                simp [MulAdd.eq.AddMulS]
                simp [MulMul.eq.Mul_Mul]
                rw [← ProdTail.eq.MulProdTakeTailTake.of.Ge h_d]
                simp [AddAdd.eq.Add_Add]
                simp only [DropTail.eq.Drop] at h_r_mod h_q_div
                simp [h_r'_mod, h_r_mod]
                simp [Add_Add.eq.AddAdd]
                rw [show (i - d + 1) = i + 1 - d by omega] at h_qₕ_div h_rₕ_mod h_rₑ_mod
                rw [TakeDropTake.eq.DropTake (by omega)] at h_qₕ_div h_rₕ_mod h_qᵢ_div h_rᵢ_mod
                rw [TakeTake.eq.Take.of.Ge (by omega)] at h_rₑ_mod
                simp [Mul_Mul.eq.MulMul] at h_rₑ_mod
                simp [h_rₐ_mod] at h_qₕ_div h_rₕ_mod
                simp [h_rₑ_mod] at h_qᵢ_div h_rᵢ_mod
                rw [show i + 1 - d = (i - d + 1) by omega] at h_qᵢ_div h_rᵢ_mod
                rw [ProdDropTake.eq.MulProdDropTake.of.Gt.GtLength h_i (by omega)] at h_qₕ_div h_rₕ_mod h_qᵢ_div h_rᵢ_mod
                simp [show (i - d + 1) = i + 1 - d by omega] at h_qₕ_div h_rₕ_mod
                rw [DivMod_Mul.eq.ModDiv] at h_qₕ_div h_qᵢ_div
                simp [h_q_div] at h_qₕ_div h_rₕ_mod h_qₐ_div h_rₐ_mod
                simp [h_qₕ_div, h_qᵢ_div]
                simp [h_rₕ_mod, h_rᵢ_mod]
                simp [show i + 1 - d = (i - d + 1) by omega]
                left
                simp [AddAdd.eq.Add_Add] at h_qₐ_div
                rw [h_qₐ_div]
              repeat rw [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS]
            repeat rw [ProdAppend.eq.MulProdS]
          ·
            simp only [h_toNat]
            simp [Permute__Neg.eq.Append_AppendRotateDropTake]
            simp [Mul_Mul.eq.MulMul]
            repeat rw [EqMin.of.Le (by omega)]
            simp
        ·
          simp only [h_toNat]
          simp
          rw [TailPermute__Neg.eq.PermuteTail.of.Gt (by simp; omega)]
          simp [Permute__Neg.eq.Append_AppendRotateDropTake]
          simp [Mul_Mul.eq.MulMul]
          repeat rw [EqMin.of.Le (by omega)]
          simp


-- created on 2025-12-02
-- updated on 2025-12-03
