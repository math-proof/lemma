import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.Drop.eq.AppendTakeDrop
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.DropPermute__Neg.eq.Drop
import Lemma.List.DropPermute__Neg.eq.TakeDrop.of.Add.eq.SubLength_1
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.DropTakeDrop.eq.DropTake
import Lemma.List.EqPermutePermute__Neg.of.In_Ioo_Length
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.GetPermute__Neg.eq.Get_Add.of.GtLength_Add
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.Append_RotateDropTake.of.EqLength_Add_1
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDrop.eq.Get.of.EqLength_Add_1
import Lemma.List.ProdDropPermute__Neg.eq.ProdDrop.of.Add.eq.SubLength_1
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTakeDrop.eq.Get.of.Lt_Length
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailTakeDrop.eq.TakeDrop
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.Nat.Add
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtVal
import Lemma.Nat.Mul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.Sub_Sub.eq.Min
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat List Bool Tensor Vector
set_option maxHeartbeats 1600000


@[main]
private lemma main
  [NeZero (d : ℕ)]
  [NeZero (i : ℕ)]
  {s : List ℕ}
-- given
  (h : i + d = s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  (X.permute ⟨i + d, by omega⟩ (-d)).permute ⟨i, by simp; omega⟩ d ≃ X := by
-- proof
  intro h_d
  have h_i_eq : i = s.length - (d + 1) := by omega
  rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := d)]
  simp
  have h_i := NeZero.pos i
  split_ifs
  repeat omega
  have h_permute := EqPermutePermute__Neg.of.In_Ioo_Length (s := s) (i := i + d) (j := i) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  apply SEq.of.SEqDataS.Eq h_permute
  apply SEqCast.of.SEq.Eq.Eq
  ·
    rw [MulProdS.eq.ProdAppend]
    rw [Permute.eq.Append_AppendRotateTakeDrop]
  ·
    rw [h_permute]
  ·
    apply SEq.of.All_EqGetS.Eq
    ·
      intro t
      have h_t := LtVal t
      let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
      simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
      unfold Tensor.permuteHead
      simp
      have h_r := LtVal r
      simp only [ProdAppend.eq.MulProdS] at h_r
      rw [GetCast.eq.Get.of.Eq.Lt h_r]
      ·
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
        let ⟨h_q'_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        rw [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
        unfold Tensor.rotate
        simp [GetElem.getElem]
        have h_q' := LtVal q'
        have h_r' := LtVal r'
        simp at h_r'
        simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q'
        rw [GetCast.eq.Get.of.Eq.Lt.fin h_q']
        ·
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q'
          have h_qₐ := LtVal qₐ
          have h_rₐ := LtVal rₐ
          simp at h_qₐ h_rₐ
          have h_1_lt_d1 : 1 < d + 1 := by omega
          rw [EqMin.of.Le (by omega), EqMod.of.Lt h_1_lt_d1] at h_qₐ h_rₐ
          rw [DropTakeDrop.eq.DropTake] at h_qₐ
          have h_length_eq_add_1 : s.length = i + d + 1 := by omega
          simp [Add.comm (a := d), ← h_length_eq_add_1] at h_qₐ
          rw [EqTake.of.Ge_Length (n := s.length) (by simp)] at h_qₐ
          rw [DropPermute__Neg.eq.TakeDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) (by omega)] at h_qₐ
          rw [TakeTake.eq.Take.of.Gt (show d + 1 > 1 by omega)] at h_rₐ
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
          simp
          rw [DataCast.eq.Cast_Data.of.Eq]
          ·
            simp
            rw [Add_Add.eq.AddAdd (a := i), ← h_length_eq_add_1] at h_r'
            rw [Drop.eq.Nil.of.Ge_Length (i := s.length) (by simp)] at h_r'
            simp at h_r'
            simp [h_r']
            have h_Ltqₐrₐ : rₐ * ((s.drop i).take d).prod + qₐ < ((s.permute ⟨i + d, by grind⟩ (-d)).drop i).prod := by
              rw [Prod.eq.MulProdTake__ProdDrop ((s.permute ⟨i + d, by grind⟩ (-d)).drop i) 1]
              simp
              rw [DropPermute__Neg.eq.TakeDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) (by omega)]
              apply AddMul.lt.Mul.of.Lt.Lt h_rₐ h_qₐ
            have h_lt : q * ((s.permute ⟨i + d, by grind⟩ (-(d : ℤ))).drop i).prod + (rₐ * ((((s.permute ⟨i + d, by grind⟩ (-(d : ℤ))).drop i).take (d + 1)).drop (1 % ((d + 1) ⊓ (s.length - i)))).prod + qₐ) * ((s.permute ⟨i + d, by grind⟩ (-(d : ℤ))).drop (i + (d + 1))).prod < (s.take (s.length - (1 - -(d : ℤ)).toNat)).prod * ((s.drop (s.length - (1 - -(d : ℤ)).toNat)).rotate ((1 - -(d : ℤ)).toNat ⊓ s.length - 1)).prod := by
              rw [h_toNat]
              simp [← h_i_eq]
              rw [EqMin.of.Le (by omega), EqMod.of.Lt h_1_lt_d1]
              rw [EqMin.of.Lt (by omega), EqSubAdd]
              rw [Add_Add.eq.AddAdd (a := i)]
              rw [DropPermute__Neg.eq.Drop ⟨i + d, by grind⟩]
              simp [← h_length_eq_add_1]
              simp [TailTakeDrop.eq.TakeDrop]
              rw [TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add (by omega)]
              simp [ProdRotate.eq.Prod]
              rw [← ProdPermute.eq.Prod (s := s) ⟨i + d, by omega⟩ (-d)]
              rw [Prod.eq.MulProdTake__ProdDrop (s.permute ⟨i + d, by omega⟩ (-d)) i]
              apply AddMul.lt.Mul.of.Lt.Lt
              ·
                grind
              ·
                simpa
            rw [GetCast.eq.Get.of.Eq.Lt.fin h_lt]
            ·
              let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
              simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
              unfold Tensor.rotate
              simp
              have h_rₑ := LtVal rₑ
              simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_rₑ
              rw [GetCast.eq.Get.of.Eq.Lt.fin h_rₑ]
              ·
                let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_rₑ
                let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                apply congrArg
                simp only [h_toNat]
                have h_d1_le_length :  d + 1 ≤ s.length := by omega
                simp [EqMin.of.Le h_d1_le_length]
                rw [Sub_Sub.eq.Min]
                simp [EqMin.of.Ge h_d1_le_length]
                simp [← h_i_eq]
                rw [ProdDrop.eq.Get.of.EqLength_Add_1 (n := i + d) (by omega)]
                simp only [h_toNat] at h_qₑ_div
                simp [h_qₑ_div]
                repeat rw [EqMin.of.Le (by omega)]
                rw [EqSubAdd, EqMod.of.Lt (show d + 1 > 1 by omega)]
                rw [Add_Add.eq.AddAdd (a := i)]
                rw [DropPermute__Neg.eq.Drop ⟨i + d, by grind⟩]
                rw [Drop.eq.Nil.of.Ge_Length (i := i + d + 1) (by omega)]
                simp [← h_i_eq]
                rw [ProdRotate.eq.Prod]
                rw [TailTakeDrop.eq.TakeDrop]
                rw [TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add (by omega)]
                simp [h_qr]
                rw [Add_Add.eq.AddAdd (a := i)]
                rw [DropPermute__Neg.eq.Drop ⟨i + d, by grind⟩]
                rw [Drop.eq.Nil.of.Ge_Length (i := i + d + 1) (by omega)]
                simp
                rw [ProdRotate.eq.Prod]
                simp [TakeDrop.eq.DropTake (j := d + 1)]
                rw [Add_Add.eq.AddAdd (a := i)]
                simp [← h_length_eq_add_1]
                rw [EqTake.of.Ge_Length (n := s.length) (by simp)]
                rw [ProdDropPermute__Neg.eq.ProdDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) (by omega)]
                rw [DivAddMul.eq.Add_Div.of.Gt_0]
                ·
                  simp [MulAdd.eq.AddMulS, AddAdd.eq.Add_Add]
                  rw [ProdDropPermute__Neg.eq.ProdDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) (by omega)] at h_Ltqₐrₐ
                  simp at h_Ltqₐrₐ
                  simp [Div.eq.Zero.of.Lt h_Ltqₐrₐ]
                  simp [h_q'r', h_r']
                  rw [Drop.eq.Nil.of.Ge_Length (i := i + (d + 1)) (by simp; omega)]
                  simp
                  simp only [h_toNat] at h_qₕ_div h_rₕ_mod
                  simp [Sub_Sub.eq.Min, EqMin.of.Ge h_d1_le_length] at h_qₕ_div h_rₕ_mod
                  simp [EqMin.of.Le h_d1_le_length] at h_qₕ_div h_rₕ_mod
                  simp [← h_i_eq] at h_qₕ_div h_rₕ_mod
                  simp [h_qₕ_div, h_rₕ_mod]
                  simp [h_qₐrₐ]
                  simp only [h_toNat, ← h_i_eq] at h_rₑ
                  simp at h_rₑ
                  simp [EqMin.of.Le h_d1_le_length] at h_rₑ
                  rw [EqMod.of.Lt (by omega), Mul.comm, MulProdS.eq.ProdAppend] at h_rₑ
                  rw [← Drop.eq.AppendTakeDrop] at h_rₑ
                  simp only [h_toNat, ← h_i_eq] at h_rₑ_mod
                  simp [EqMin.of.Le h_d1_le_length] at h_rₑ_mod
                  simp [ProdRotate.eq.Prod] at h_rₑ_mod
                  rw [Add_Add.eq.AddAdd (a := i)] at h_rₑ_mod
                  rw [DropPermute__Neg.eq.Drop ⟨i + d, by grind⟩] at h_rₑ_mod
                  rw [Drop.eq.Nil.of.Ge_Length (i := i + d + 1) (by omega)] at h_rₑ_mod
                  simp at h_rₑ_mod
                  rw [EqMin.of.Le (show d + 1 ≤ s.length - i by omega)] at h_rₑ_mod
                  rw [EqMod.of.Lt h_1_lt_d1] at h_rₑ_mod
                  simp [TakeDrop.eq.DropTake] at h_rₑ_mod
                  rw [EqTake.of.Ge_Length (n := i + (d + 1)) (by simp; omega)] at h_rₑ_mod
                  rw [DropPermute__Neg.eq.TakeDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) (by omega)] at h_rₑ_mod
                  rw [ProdDropPermute__Neg.eq.ProdDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) (by omega)] at h_rₑ_mod
                  simp at h_rₑ_mod
                  rw [EqMod.of.Lt h_Ltqₐrₐ] at h_rₑ_mod
                  simp [h_rₑ_mod]
                  rw [DivAddMul.eq.Add_Div.of.Gt_0]
                  ·
                    rw [EqMin.of.Le (by omega)]
                    rw [EqMod.of.Lt h_1_lt_d1]
                    rw [EqMod.of.Lt h_qₐ]
                    simp [Div.eq.Zero.of.Lt h_qₐ]
                    left
                    simp [TakeDrop.eq.DropTake]
                    rw [EqTake.of.Ge_Length (n := i + (d + 1)) (by simp; omega)]
                    simp [DropTake.eq.TakeDrop]
                    rw [ProdTakeDrop.eq.Get.of.Lt_Length (i := i) (s := s.permute ⟨i + d, by grind⟩ (-d)) (by simp; omega)]
                    simp [GetPermute__Neg.eq.Get_Add.of.GtLength_Add]
                  ·
                    grind
                ·
                  rw [ProdRotate.eq.Prod] at h_r
                  rw [MulProdS.eq.ProdAppend] at h_r
                  simp at h_r
                  rw [ProdDropPermute__Neg.eq.ProdDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) (by omega)] at h_r
                  grind
              ·
                rw [MulProdS.eq.ProdAppend]
                rw [Rotate.eq.AppendDrop__Take]
            ·
              rw [h_toNat]
              rw [MulProdS.eq.ProdAppend]
              rw [EqMin.of.Lt (by omega), EqSubAdd]
              simp [← h_i_eq]
              rw [MulProdS.eq.ProdAppend]
              rw [Permute__Neg.eq.Append_RotateDropTake.of.EqLength_Add_1 h_length_eq_add_1]
          ·
            rw [h_toNat]
            simp [Permute__Neg.eq.Append_AppendRotateTakeDrop]
            rw [TakeTake.eq.Take.of.Gt (by omega)]
            simp [← h_i_eq]
            rw [EqMin.of.Lt (by omega), EqSubAdd]
            rw [EqTake.of.Ge_Length (by omega)]
            rw [Drop.eq.Nil.of.Ge_Length (i := i + d + 1) (by omega)]
            simp
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [Rotate.eq.AppendDrop__Take]
      ·
        rw [MulProdS.eq.ProdAppend]
    ·
      rw [MulProdS.eq.ProdAppend]
      apply congrArg
      rwa [← Permute.eq.Append_AppendRotateTakeDrop (i := ⟨i, by simp; omega⟩) (d := d)]


-- created on 2025-10-26
-- updated on 2025-10-28
