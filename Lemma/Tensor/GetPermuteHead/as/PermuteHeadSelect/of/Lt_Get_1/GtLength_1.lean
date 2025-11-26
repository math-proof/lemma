import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EraseIdxTail.eq.Drop_2
import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.Lt_LengthTail
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.GetRotate.eq.Ite.of.GeLength.GtLength
import Lemma.List.Get_0.dvd.ProdTakeEraseIdx.of.Gt_0.Gt_0.GtLength_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.LengthEraseIdx.ge.SubLength_1
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.Prod.eq.Mul_ProdEraseIdx.of.GtLength
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.List.ProdEraseIdx.eq.MulProdS.of.Lt
import Lemma.List.ProdEraseIdx.eq.Mul_ProdDrop_2
import Lemma.List.ProdEraseIdx.eq.Mul_ProdDrop_2.of.GtLength_0
import Lemma.List.ProdProd.dvd.ProdEraseIdx.of.Gt
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTakeEraseIdx.eq.MulProdTakeDrop_2.of.Gt_0.GtLength_0
import Lemma.List.ProdTakeEraseIdx_1.eq.Get_0.of.GtLength_0
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.Tail.eq.Drop_1
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TailEraseIdx.eq.Drop_2
import Lemma.List.TailPermute.eq.PermuteEraseIdx.of.GtLength_1
import Lemma.List.TailRotateTake.eq.RotateTakeEraseIdx.of.GtLength_1
import Lemma.List.TailTail.eq.Drop_2
import Lemma.List.TailTakeEraseIdx.eq.TakeDrop.of.Gt_0
import Lemma.List.TakeEraseIdx.eq.EraseIdxTake.of.Le
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.Dvd_Mul
import Lemma.Nat.Dvd_Mul.of.Dvd
import Lemma.Nat.EqAddS.is.Eq
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Mod.le.Max
import Lemma.Nat.ModAdd.eq.Mod.of.Dvd
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.LengthPermuteHead.eq.Get_1.of.GtLength_1.Gt_1
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
  {k : ℕ}
-- given
  (h : s.length > 1)
  (h_k : k < s[1])
  (X : Tensor α s) :
-- imply
  (X.permuteHead (d + 1)).get ⟨k, by rwa [LengthPermuteHead.eq.Get_1.of.GtLength_1.Gt_1 (by linarith [NeZero.pos d]) h]⟩ ≃ (X.select ⟨1, by grind⟩ ⟨k, h_k⟩).permuteHead d := by
-- proof
  have h_d := NeZero.pos d
  unfold permuteHead
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    rw [TailAppend.eq.AppendTail.of.GtLength_0]
    ·
      rw [DropEraseIdx.eq.Drop.of.Le (by omega)]
      simp
      apply TailRotateTake.eq.RotateTakeEraseIdx.of.GtLength_1 h
    ·
      simp
      omega
  ·
    simp
    rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, ?_⟩)]
    ·
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        rw [MulProdS.eq.ProdAppend]
      ·
        simp
        apply SEq.of.All_EqGetS.Eq
        ·
          intro t
          have h_t := t.isLt
          simp only [GetElem.getElem]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [GetCast.eq.Get.of.Eq.fin]
          simp at h_t
          simp [TailAppend.eq.AppendTail.of.GtLength_0 (show ((s.take (d + 1)).rotate 1).length > 0 by simp; omega)] at h_t ⊢
          simp [TailRotateTake.eq.RotateTakeEraseIdx.of.GtLength_1 h] at h_t ⊢
          simp [ProdRotate.eq.Prod]
          simp only [← DropEraseIdx.eq.Drop.of.Le (i := 1) (j := d) (by omega)] at h_t ⊢
          simp
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          have h_q := q.isLt
          have h_r := r.isLt
          simp [ProdRotate.eq.Prod] at h_t
          let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
          have h_lt : k * (s.eraseIdx 1).prod + ↑t < ((s.take (d + 1)).rotate 1).prod * (s.drop (d + 1)).prod := by
            simp [ProdRotate.eq.Prod]
            rw [Prod.eq.Mul_ProdEraseIdx.of.GtLength h]
            exact AddMul.lt.Mul.of.Lt.Lt h_k h_t
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
          have h_q' := q'.isLt
          simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q' h_q
          let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          unfold Tensor.rotate
          simp
          repeat rw [GetCast.eq.Get.of.Eq.fin]
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
          let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
          have h_qₐ := qₐ.isLt
          have h_rₐ := rₐ.isLt
          simp at h_qₐ h_rₐ
          let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q'
          let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
          have h_qₑ := qₑ.isLt
          have h_rₑ := rₑ.isLt
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          repeat rw [GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          unfold select
          simp
          rw [DataCast.eq.Cast_Data.of.Eq]
          ·
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              rw [DataFromVector.eq.FlattenMapData]
              have h_lt : (↑rₐ * (((s.eraseIdx 1).take d).drop (1 % (d ⊓ (s.eraseIdx 1).length))).prod + ↑qₐ) * ((s.eraseIdx 1).drop d).prod + ↑r < s.headD 1 * (s.tail.eraseIdx 0).prod := by
                rw [EraseIdxTail.eq.Drop_2]
                rw [← ProdEraseIdx.eq.Mul_ProdDrop_2]
                rw [Prod.eq.MulProdS (s.eraseIdx 1) d]
                apply AddMul.lt.Mul.of.Lt.Lt _ h_r
                rw [Prod.eq.MulProdS ((s.eraseIdx 1).take d) (1 % (d ⊓ (s.eraseIdx 1).length))]
                apply AddMul.lt.Mul.of.Lt.Lt h_rₐ h_qₐ
              let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
              simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
              rw [Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0]
              rw [DataCast.eq.Cast_Data.of.Eq (by simp)]
              simp [GetCast.eq.Get.of.Eq.fin]
              rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, ?_⟩)]
              ·
                rw [GetCast.eq.Get.of.Eq.fin]
                ·
                  simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  unfold Tensor.toVector
                  rw [GetCast.eq.Get.of.Eq.fin]
                  ·
                    simp [GetCast.eq.Get.of.Eq.fin]
                    simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    apply congrArg
                    simp
                    simp only [EraseIdxTail.eq.Drop_2] at h_rₕ_mod
                    simp [DropEraseIdx.eq.Drop.of.Le (show d ≥ 1 by omega)] at *
                    rw [ModAdd.eq.Mod.of.Dvd.left] at h_r'_mod
                    ·
                      have h_r_eq : r' = r.val := by grind
                      simp [h_r_eq]
                      have h_1_lt_min : 1 < ((d + 1) ⊓ s.length) := by omega
                      rw [EqMod.of.Lt h_1_lt_min]
                      rw [DropTake.eq.TakeDrop]
                      simp [Add.comm (a := d) (b := 1)]
                      rw [Drop_Add.eq.DropDrop, Drop_1.eq.Tail]
                      rw [MulAdd.eq.AddMulS]
                      rw [MulMul.eq.Mul_Mul]
                      rw [MulProdS.eq.Prod]
                      simp
                      apply Eq.of.EqAddS (a := ↑qₕ * s.tail.tail.prod)
                      rw [Add_Add.eq.AddAdd]
                      conv_rhs =>
                        rw [AddAdd.eq.Add_Add]
                      conv_rhs at h_qₕrₕ =>
                        rw [Add.comm]
                      rw [← h_qₕrₕ]
                      rw [Add_Add.eq.AddAdd]
                      rw [AddAdd.comm]
                      simp
                      rw [ProdEraseIdx.eq.MulProdS.of.Lt (d := d + 1) (by omega)] at h_q'_div
                      rw [Mul_Mul.eq.MulMul] at h_q'_div
                      rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_q'_div
                      simp [← h_q_div] at h_q'_div
                      rw [← TakeEraseIdx.eq.EraseIdxTake.of.Le (by omega)] at h_q'_div
                      simp [h_q'_div] at h_qₑ_div h_rₑ_mod
                      simp [EqMod.of.Lt h_1_lt_min] at h_qₑ_div h_rₑ_mod
                      rw [TakeTake.eq.Take.of.Ge (show d + 1 ≥ 1 by simp)] at h_qₑ_div h_rₑ_mod
                      have := Mod.le.Max 1 (d ⊓ (s.eraseIdx 1).length)
                      rw [TakeTake.eq.Take.of.Ge (show d ≥ (1 % (d ⊓ (s.eraseIdx 1).length)) by omega)] at h_qₐ_div h_rₐ_mod
                      have h_length_ge := LengthEraseIdx.ge.SubLength_1 s 1
                      have h_prod := ProdDrop.eq.MulProdS (s := s) 2 (d - 1)
                      simp [show 2 + (d - 1) = d + 1 by omega] at h_prod
                      rw [ProdEraseIdx.eq.Mul_ProdDrop_2.of.GtLength_0 (by omega)] at h_t
                      if h_d : d = 1 then
                        subst h_d
                        simp
                        have h_q := q.isLt
                        simp [ProdRotate.eq.Prod] at h_q
                        have h_s_len : (s.eraseIdx 1).length ≥ 1 := by simp; omega
                        have h_mod_eq_0 : 1 % (1 ⊓ (s.eraseIdx 1).length) = 0 := by
                          simp [EqMin.of.Le h_s_len]
                        simp [h_mod_eq_0] at *
                        rw [EqMin.of.Le (by omega)] at h_rₑ
                        simp at h_rₑ
                        rw [TakeTake.eq.Take.of.Ge (show 2 ≥ 1 by omega)] at h_rₑ
                        rw [TailTail.eq.Drop_2] at ⊢ h_qₕ_div
                        rw [ProdTakeEraseIdx_1.eq.Get_0.of.GtLength_0 (by omega)] at *
                        simp [h_rₐ] at ⊢ h_qₕ_div
                        rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)] at *
                        rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₕ_div h_qₑ_div
                        rw [Div.eq.Zero.of.Lt (by assumption)] at h_qₕ_div h_qₑ_div
                        simp at h_rₑ_mod
                        rw [EqMod.of.Lt h_q] at h_rₑ_mod
                        simp [h_qₕ_div, h_qₑ_div]
                        left
                        simp [h_rₑ_mod]
                        grind
                      else if h : s.length = 2 then
                        have h_q := q.isLt
                        simp [ProdRotate.eq.Prod] at h_q
                        have h_length_eq_1 := LengthEraseIdx.eq.SubLength_1.of.GtLength (by omega)
                        have h_mod_eq_0 : 1 % (d ⊓ (s.eraseIdx 1).length) = 0 := by
                          simp [h_length_eq_1]
                          omega
                        simp [h_mod_eq_0] at *
                        rw [h, EqMin.of.Ge (by omega)] at h_rₑ
                        rw [TakeTake.eq.Take.of.Ge (show d + 1 ≥ 1 by omega)] at h_rₑ
                        rw [TailTail.eq.Drop_2] at *
                        simp [h_rₐ] at *
                        rw [ProdTake_1.eq.Get_0.of.GtLength_0 (show s.length > 0 by omega)] at *
                        simp [h_qₐ_div] at *
                        simp [← h_qr] at h_qₕ_div h_rₕ_mod
                        rw [ProdTakeEraseIdx.eq.MulProdTakeDrop_2.of.Gt_0.GtLength_0 (by omega) (by omega)] at h_qₑ_div
                        rw [Mul_Mul.eq.MulMul] at h_qₑ_div
                        rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₑ_div
                        rw [ModAdd.eq.Mod.of.Dvd.left] at h_rₑ_mod
                        ·
                          simp [h_qₑ_div]
                          rw [MulAdd.eq.AddMulS]
                          rw [MulMul.eq.Mul_Mul]
                          simp [← h_prod]
                          rw [AddAdd.comm]
                          conv_rhs => rw [AddAdd.comm]
                          rw [Add_Add.eq.AddAdd]
                          rw [AddAdd.comm]
                          simp [Drop.eq.Nil.of.Ge_Length (show 2 ≥ s.length by omega)] at *
                          simp [Drop.eq.Nil.of.Ge_Length (show d + 1 ≥ s.length by omega)] at *
                          simp [h_q_div] at h_rₑ_mod
                          rw [EqMod.of.Lt h_t] at h_rₑ_mod
                          simp [h_rₑ_mod, h_qₕ_div, h_q_div]
                          right
                          exact h_t
                        ·
                          apply Dvd_Mul.of.Dvd
                          apply Get_0.dvd.ProdTakeEraseIdx.of.Gt_0.Gt_0.GtLength_1
                          repeat omega
                      else
                        have h_min_gt_1 : d ⊓ (s.eraseIdx 1).length > 1 := by
                          simp
                          constructor
                          repeat omega
                        have h_mod_eq_1 := EqMod.of.Lt h_min_gt_1
                        simp [h_mod_eq_1] at *
                        have h_min_gt_1 : (d + 1) ⊓ s.length > 1 := by
                          simp
                          constructor
                          repeat omega
                        have h_mod_eq_1 := EqMod.of.Lt h_min_gt_1
                        simp [h_mod_eq_1] at *
                        rw [TakeTake.eq.Take.of.Ge (show d + 1 ≥ 1 by omega)] at *
                        rw [TailTail.eq.Drop_2] at *
                        rw [ProdTake_1.eq.Get_0.of.GtLength_0 (show s.length > 0 by omega)] at *
                        rw [ProdTakeEraseIdx_1.eq.Get_0.of.GtLength_0 (by omega)] at *
                        rw [ProdTakeEraseIdx.eq.MulProdTakeDrop_2.of.Gt_0.GtLength_0 (by omega) (by omega)] at *
                        rw [Mul_Mul.eq.MulMul] at h_qₑ_div
                        rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₑ_div
                        rw [ModAdd.eq.Mod.of.Dvd.left] at h_rₑ_mod
                        ·
                          simp [h_qₑ_div]
                          rw [TailTakeEraseIdx.eq.TakeDrop.of.Gt_0 _ (by omega)] at *
                          rw [MulAdd.eq.AddMulS, MulMul.eq.Mul_Mul] at *
                          rw [MulAdd.eq.AddMulS, MulMul.eq.Mul_Mul]
                          rw [← h_prod] at ⊢ h_qₕ_div
                          rw [AddAdd.eq.Add_Add] at h_qₕ_div
                          rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₕ_div
                          rw [AddAdd.comm]
                          conv_rhs => rw [AddAdd.comm]
                          rw [Add_Add.eq.AddAdd]
                          rw [AddAdd.comm]
                          rw [Add_Add.eq.AddAdd]
                          simp [h_rₑ_mod, h_qₐ_div, h_rₐ_mod] at *
                          simp [h_qₕ_div]
                          repeat rw [MulAdd.eq.AddMulS]
                          simp [AddAdd.eq.Add_Add]
                          simp [Add.comm]
                          repeat right
                          rw [Add.comm]
                          rw [h_prod]
                          apply Nat.AddMul.lt.Mul.of.Lt.Lt h_qₐ h_r
                        ·
                          apply Dvd_Mul.of.Dvd
                          apply Dvd_Mul
                    ·
                      apply Dvd_Mul.of.Dvd
                      apply ProdProd.dvd.ProdEraseIdx.of.Gt
                      omega
                  ·
                    apply ProdTake_1.eq.HeadD_1
                ·
                  simp [TailTail.eq.Drop_2]
              ·
                simpa
              ·
                simpa
            ·
              rw [EraseIdx.eq.Cons_EraseIdxTail.of.Lt_LengthTail]
              simp
              omega
          ·
            rw [EraseIdx.eq.Cons_EraseIdxTail.of.Lt_LengthTail]
            simp
            omega
          repeat {
            rw [MulProdS.eq.ProdAppend]
            rw [Rotate.eq.AppendDrop__Take]
          }
        ·
          rw [MulProdS.eq.ProdAppend]
          apply congrArg
          rw [← Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (by omega)]
          have := Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (s := s.eraseIdx 1) (by rw [LengthEraseIdx.eq.SubLength_1.of.GtLength (by omega)]; omega) (d - 1)
          rw [EqAddSub.of.Ge (by omega)] at this
          rw [← this]
          simp
          exact TailPermute.eq.PermuteEraseIdx.of.GtLength_1.pos h
    ·
      simp
      omega
    ·
      rw [GetAppend.eq.Get.of.GtLength]
      ·
        rw [GetRotate.eq.Ite.of.GeLength.GtLength]
        ·
          simp
          split_ifs
          ·
            assumption
          ·
            omega
        repeat {
          simp
          omega
        }
      ·
        simp
        omega


-- created on 2025-11-02
-- updated on 2025-11-04
