import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Drop.eq.AppendTakeDrop
import Lemma.List.DropPermute__Neg.eq.Cons_TakeDrop.of.GtLength_Add
import Lemma.List.DropPermute__Neg.eq.Drop
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.DropTakeDrop.eq.DropTake
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.List.EqPermutePermute__Neg.of.In_Ioo_Length
import Lemma.List.GetPermute__Neg.eq.Get_Add.of.GtLength_Add
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop.of.GtLength_Add_1
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTakeDrop.eq.Get.of.GtLength
import Lemma.List.ProdTakeDrop.eq.MulProdTakeDrop.of.GtLength_Add
import Lemma.List.ProdTakeDrop.eq.Mul_ProdTakeDrop.of.GtLength_Add
import Lemma.List.ProdTakeDropPermute__Neg.eq.ProdTakeDrop.of.GtLength_Add
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add
import Lemma.List.TakeDropTake.eq.TakeDrop
import Lemma.List.TakePermute__Neg.eq.Take.of.GtLength_Add
import Lemma.List.TakeTake.eq.Take
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.Nat.Add
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.AddMulAddMul.lt.MulMul.of.Lt.Lt.Lt
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.EqAddS.is.Eq
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Mul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Nat Bool Tensor Vector Fin
set_option maxHeartbeats 1600000


@[main]
private lemma main
  [NeZero (d : ℕ)]
  [NeZero (i : ℕ)]
  {s : List ℕ}
-- given
  (h : i + d < s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  have h_id : i + d < s.length := by omega
  (X.permute ⟨i + d, h_id⟩ (-d)).permute ⟨i, by simp; omega⟩ d ≃ X := by
-- proof
  intro h_d h_id
  have h_i_pos := NeZero.pos i
  rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := d)]
  simp
  have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := i) (j := i + d) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  have h_toNatSub := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  split_ifs
  repeat omega
  have h_permute := EqPermutePermute__Neg.of.In_Ioo_Length (s := s) (i := i + d) (j := i) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  apply SEq.of.SEqDataS.Eq h_permute
  apply SEqCast.of.SEq.Eq
  ·
    rw [MulProdS.eq.ProdAppend]
    rw [Permute.eq.Append_AppendRotateTakeDrop]
  ·
    apply SEq.of.All_EqGetS.Eq
    ·
      intro t
      have h_t := t.isLt
      let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
      simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
      unfold Tensor.permuteHead
      have h_r := r.isLt
      simp only [ProdAppend.eq.MulProdS] at h_r
      simp [GetElem.getElem]
      rw [GetCast.eq.Get.of.Eq.fin]
      ·
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_r
        let ⟨h_q'_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
        unfold Tensor.rotate
        have h_q' := q'.isLt
        have h_r' := r'.isLt
        simp at h_r'
        simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q'
        repeat rw [GetCast.eq.Get.of.Eq.fin]
        ·
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_q'
          have h_qₐ := qₐ.isLt
          have h_rₐ := rₐ.isLt
          simp at h_qₐ h_rₐ
          have h_1_lt_d1 : 1 < d + 1 := by omega
          rw [EqMin.of.Le (by omega), EqMod.of.Lt h_1_lt_d1] at h_qₐ h_rₐ
          rw [DropTakeDrop.eq.DropTake] at h_qₐ
          simp [DropTake.eq.TakeDrop] at h_qₐ
          rw [TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add] at h_qₐ
          rw [TakeTake.eq.Take.of.Gt h_1_lt_d1] at h_rₐ
          let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
          rw [GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [@Tensor.Permute.eq.Ite (i := ⟨i + d, by omega⟩) (d := -d)]
          simp
          split_ifs
          repeat omega
          have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
          rw [Add.comm] at h_toNat
          unfold Tensor.permuteTail
          have h_d1_le_length : d + 1 ≤ s.length - i := by omega
          simp [EqMin.of.Le h_d1_le_length]
          simp [EqMod.of.Lt h_1_lt_d1]
          simp [Add_Add.eq.AddAdd (a := i)]
          simp [DropPermute__Neg.eq.Drop ⟨i + d, by omega⟩]
          simp [DropPermute__Neg.eq.Cons_TakeDrop.of.GtLength_Add h_id]
          simp [TakeAppend.eq.Take.of.GeLength (show d ≤ ((s.drop i).take d).length by simp; omega)]
          simp [TakeTake.eq.Take]
          rw [ProdTakeDrop.eq.Get.of.GtLength (by simp; omega)] at h_rₐ
          rw [GetPermute__Neg.eq.Get_Add.of.GtLength_Add (by omega)] at h_rₐ
          rw [Add_Add.eq.AddAdd] at h_r'
          rw [DropPermute__Neg.eq.Drop ⟨i + d, by grind⟩] at h_r'
          have h_lt : q * (s[i + d] * (((s.drop i).take d).prod * (s.drop (i + d + 1)).prod)) + ((rₐ * ((s.drop i).take d).prod + qₐ) * (s.drop (i + d + 1)).prod + r') < ((s.take (i + d + 1)).take ((s.take (i + d + 1)).length - (1 - -(d : ℤ)).toNat) ++ ((s.take (i + d + 1)).drop ((s.take (i + d + 1)).length - (1 - -(d : ℤ)).toNat)).rotate ((1 - -(d : ℤ)).toNat ⊓ (s.take (i + d + 1)).length - 1)).prod * (s.drop (i + d + 1)).prod := by
            rw [h_toNat]
            simp
            repeat rw [EqMin.of.Le (by omega)]
            rw [AddAdd.eq.Add_Add]
            repeat rw [EqSubAdd]
            rw [TakeTake.eq.Take.of.Gt (show i + (d + 1) > i by omega)]
            rw [← TakeDrop.eq.DropTake]
            rw [MulProdS.eq.ProdAppend]
            rw [Add_Add.eq.AddAdd (a := i)]
            rw [MulProdS.eq.ProdAppend]
            simp [ProdRotate.eq.Prod]
            rw [ProdTakeDrop.eq.Mul_ProdTakeDrop.of.GtLength_Add h_id]
            rw [MulMul.eq.Mul_Mul (a := (s.take i).prod)]
            rw [MulMul.eq.Mul_Mul (a := s[i + d])]
            apply AddMul.lt.Mul.of.Lt.Lt
            ·
              have h_q := q.isLt
              simp [TakePermute__Neg.eq.Take.of.GtLength_Add h_id] at h_q
              exact h_q
            ·
              rw [Mul_Mul.eq.MulMul (a := s[i + d])]
              apply AddMulAddMul.lt.MulMul.of.Lt.Lt.Lt h_rₐ h_qₐ h_r'
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
            let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
            have h_qₑ := qₑ.isLt
            simp only [ProdAppend.eq.MulProdS] at h_qₑ
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_qₑ
              let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
              have h_rₕ := rₕ.isLt
              simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_rₕ
              simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
              unfold Tensor.rotate
              simp
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                let ⟨qᵢ, rᵢ, h_qᵢrᵢ⟩ := Any_Eq_AddMul.of.Lt_Mul h_rₕ
                let ⟨h_qᵢ_div, h_rᵢ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qᵢrᵢ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qᵢrᵢ]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                apply congrArg
                simp only [h_toNat]
                simp
                rw [EqMin.of.Le (by omega)]
                rw [EqMin.of.Le (show d + 1 ≤ i + d + 1 by omega)]
                simp [AddAdd.eq.Add_Add (a := i)]
                rw [← TakeDrop.eq.DropTake]
                rw [Add_Add.eq.AddAdd (a := i)]
                rw [← TakeDrop.eq.DropTake]
                rw [ProdTakeDrop.eq.Get.of.GtLength (by omega)]
                simp [h_qr]
                rw [ProdRotate.eq.Prod]
                rw [Add_Add.eq.AddAdd (a := i)]
                simp [DropPermute__Neg.eq.Drop ⟨i + d, by omega⟩]
                simp [ProdTakeDropPermute__Neg.eq.ProdTakeDrop.of.GtLength_Add h_id]
                simp only [h_toNat] at h_qₕ_div
                simp at h_qₕ_div
                have h_id1_le_length : i + d + 1 ≤ s.length := by omega
                rw [EqMin.of.Le h_id1_le_length] at h_qₕ_div
                rw [EqMin.of.Le (show d + 1 ≤ i + d + 1 by omega)] at h_qₕ_div
                simp [AddAdd.eq.Add_Add (a := i)] at h_qₕ_div
                rw [ProdRotate.eq.Prod] at h_qₕ_div
                rw [← TakeDrop.eq.DropTake] at h_qₕ_div
                simp [h_qₕ_div]
                rw [Mul_Mul.eq.MulMul (a := s[i + d])] at h_qₑ_div
                rw [Mul_ProdTakeDrop.eq.ProdTakeDrop.of.GtLength_Add] at h_qₑ_div
                rw [Add_Add.eq.AddAdd] at h_qₑ_div
                rw [Mul_Mul.eq.MulMul] at h_qₑ_div
                rw [AddMulS.eq.MulAdd] at h_qₑ_div
                rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₑ_div
                simp [Div.eq.Zero.of.Lt h_r'] at h_qₑ_div
                simp [h_qₑ_div]
                have h_rₕ := rₕ.isLt
                simp only [h_toNat] at h_rₕ
                simp [ProdRotate.eq.Prod] at h_rₕ
                rw [EqMin.of.Le h_id1_le_length] at h_rₕ
                simp [AddAdd.eq.Add_Add (a := i)] at h_rₕ
                simp [DropTake.eq.TakeDrop] at h_rₕ
                rw [DivAddMul.eq.Add_Div.of.Gt_0 (by omega)]
                rw [MulAdd.eq.AddMulS]
                rw [MulMul.eq.Mul_Mul]
                rw [MulAdd.eq.AddMulS]
                repeat rw [AddAdd.eq.Add_Add]
                apply EqAddS.of.Eq.left
                simp [AddAdd.eq.Add_Add (a := i)]
                rw [MulProdS.eq.ProdAppend]
                rw [AppendTakeDrop.eq.Drop]
                rw [ProdTakeDrop.eq.MulProdTakeDrop.of.GtLength_Add h_id]
                rw [Div_Mul.eq.DivDiv]
                rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
                simp [Div.eq.Zero.of.Lt h_qₐ]
                simp [Div.eq.Zero.of.Lt h_rₐ]
                simp [h_q'r']
                rw [Add_Add.eq.AddAdd]
                rw [DropPermute__Neg.eq.Drop ⟨i + d, by omega⟩]
                simp [h_qₐrₐ]
                rw [EqMin.of.Le h_d1_le_length]
                rw [EqMod.of.Lt h_1_lt_d1]
                rw [TakeTake.eq.Take.of.Gt h_1_lt_d1]
                rw [ProdTakeDrop.eq.Get.of.GtLength (by simp; omega)]
                rw [GetPermute__Neg.eq.Get_Add.of.GtLength_Add (by omega)]
                simp only [h_toNat] at h_qᵢ_div h_rᵢ_mod h_rₕ_mod
                simp [EqMin.of.Le h_id1_le_length] at h_qᵢ_div h_rᵢ_mod h_rₕ_mod
                simp [AddAdd.eq.Add_Add (a := i)] at h_qᵢ_div h_rᵢ_mod h_rₕ_mod
                rw [Add_Add.eq.AddAdd] at h_qᵢ_div h_rᵢ_mod h_rₕ_mod
                rw [TakeDropTake.eq.TakeDrop] at h_qᵢ_div h_rᵢ_mod
                simp [h_qᵢ_div, h_rᵢ_mod]
                simp [ProdRotate.eq.Prod] at h_rₕ_mod
                simp [AddAdd.eq.Add_Add (a := i)] at h_rₕ_mod
                simp [DropTake.eq.TakeDrop] at h_rₕ_mod
                rw [ProdTakeDrop.eq.MulProdTakeDrop.of.GtLength_Add (by omega)] at h_rₕ_mod h_qₑ_div
                simp [h_rₕ_mod]
                simp [h_qₑ_div]
                rw [Mul_Mul.eq.MulMul, MulMul.comm, Add_Add.eq.AddAdd, AddMulS.eq.MulAdd]
                simp [EqMod.of.Lt h_qₐ]
                rw [MulAdd.eq.AddMulS]
                rw [MulAdd.eq.AddMulS]
                rw [AddAdd.eq.Add_Add]
                rw [AddAdd.eq.Add_Add (c := (r' : ℕ))]
                apply EqAddS.of.Eq.left
                rw [EqMod.of.Lt]
                ·
                  rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
                  rw [MulAdd.eq.AddMulS]
                  rw [AddAdd.eq.Add_Add]
                  apply EqAddS.of.Eq.left
                  simp [Div.eq.Zero.of.Lt h_qₐ]
                  simp [h_rₑ_mod]
                  rw [Add_Add.eq.AddAdd]
                  repeat rw [Mul_Mul.eq.MulMul]
                  simp [AddMulS.eq.MulAdd]
                  rw [EqMod.of.Lt h_r']
                ·
                  rw [Mul.comm (b := s[i + d])]
                  apply AddMul.lt.Mul.of.Lt.Lt h_rₐ h_qₐ
              ·
                rw [MulProdS.eq.ProdAppend]
                rw [Rotate.eq.AppendDrop__Take]
            ·
              rw [MulProdS.eq.ProdAppend]
          ·
            rw [h_toNat]
            rw [MulProdS.eq.ProdAppend]
            rw [EqMin.of.Le (by simp; omega), EqSubAdd]
            simp
            rw [EqMin.of.Le (by omega)]
            repeat rw [MulProdS.eq.ProdAppend]
            apply congrArg
            rw [AddAdd.eq.Add_Add]
            rw [EqSubAdd]
            rw [TakeTake.eq.Take.of.Gt (by omega)]
            rw [Permute__Neg.eq.Append_AppendRotateTakeDrop.of.GtLength_Add_1 (by omega)]
            rw [← TakeDrop.eq.DropTake]
            rw [AddAdd.eq.Add_Add]
        ·
          rw [MulProdS.eq.ProdAppend]
        .
          rw [Rotate.eq.AppendDrop__Take]
      ·
        rw [MulProdS.eq.ProdAppend]
    ·
      rw [MulProdS.eq.ProdAppend]
      rw [← Permute.eq.Append_AppendRotateTakeDrop (i := ⟨i, by simp; grind⟩)]
      rw [h_permute]


-- created on 2025-10-26
-- updated on 2025-10-29
