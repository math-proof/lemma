import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.DropPermute.eq.Drop.of.GtLength_0
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDropTakePermute.eq.Get_0.of.GtLength
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TakePermute.eq.TailTake.of.GtLength
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqDivAddMul.of.Lt
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Nat.LtAddMulAddMul.of.Lt.Lt.Lt.Eq
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.SubAdd.eq.AddSub.of.Ge
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Nat Vector Tensor Bool Fin
set_option maxHeartbeats 400000


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d < s.length - 1)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨0, by grind⟩ d).permute ⟨d, by simp; omega⟩ (-d) ≃ X := by
-- proof
  have h_d := NeZero.pos d
  rw [@Tensor.Permute.eq.Ite (i := ⟨d, by simp; omega⟩) (d := -d)]
  simp
  split_ifs with h_sub h_pos h_eq_d
  repeat omega
  have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := 0) (j := d) ⟨by omega, by omega⟩
  simp at h_permute
  have h_lt_add_1 := LtAdd.of.Lt_Sub h
  apply SEq.of.SEqDataS.Eq
  ·
    rw [h_permute]
  ·
    have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
    apply SEqCast.of.SEq.Eq
    ·
      rw [MulProdS.eq.ProdAppend]
      rw [h_toNat]
      simp
      rw [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]
      simp [Permute__Neg.eq.Append_AppendRotateDropTake]
    ·
      rw [h_toNat]
      unfold Tensor.permuteTail
      apply SEq.of.All_EqGetS.Eq
      ·
        have h_drop := DropPermute.eq.Drop.of.GtLength_0 (s := s) (by omega)
        intro t
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        have h_q := q.isLt
        have h_r := r.isLt
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
        simp [GetElem.getElem]
        rw [GetCast.eq.Get.of.Eq.fin]
        ·
          simp only [ProdAppend.eq.MulProdS] at h_q
          let ⟨z, q₀, h_zq₀⟩ := Any_Eq_AddMul.of.Lt_Mul h_q
          have h_z := z.isLt
          simp [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)] at h_z
          have h_q₀ := q₀.isLt
          simp only [Rotate.eq.AppendDrop__Take] at h_q₀
          have := h_q₀
          simp only [ProdAppend.eq.MulProdS] at h_q₀
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_zq₀]
          simp
          unfold Tensor.rotate
          repeat rw [GetCast.eq.Get.of.Eq.fin]
          ·
            let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_q₀
            simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
            rw [GetTranspose.eq.Get.fin]
            repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            rw [@Tensor.Permute.eq.Ite (i := ⟨0, by omega⟩) (d := d)]
            simp
            split_ifs
            unfold Tensor.permuteHead
            rw [DataCast.eq.Cast_Data.of.Eq]
            ·
              simp [h_z]
              have h_q' := q'.isLt
              have h_r' := r'.isLt
              simp [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)] at h_q' h_r'
              have h_permute := Permute.eq.AppendRotateTake___Drop.of.EqVal_0 (s := s) (i := ⟨0, by omega⟩) (by simp) d
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                unfold Tensor.rotate
                simp [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]
                have h_lt : (r' * (((s.permute ⟨0, by grind⟩ d).take (d + 1)).drop d).prod + q') * ((s.permute ⟨0, by grind⟩ d).drop (d + 1)).prod + r < ((s.take (d + 1)).rotate 1).prod * (s.drop (d + 1)).prod :=
                  LtAddMulAddMul.of.Lt.Lt.Lt.Eq (by simp [h_permute]) h_r' h_q' h_r
                let ⟨qₚ, rₚ, h_qₚrₚ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
                let ⟨h_qₚ_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₚrₚ
                simp [h_drop] at h_qₚ_div
                rw [EqDivAddMul.of.Lt (by grind)] at h_qₚ_div
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₚrₚ]
                have h_qₚ := qₚ.isLt
                rw [GetCast.eq.Get.of.Eq.fin]
                ·
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₚ
                  let ⟨qₜ, rₜ, h_qₜrₜ⟩ := Any_Eq_AddMul.of.Lt_Mul h_qₚ
                  let ⟨h_qₜ_div, h_rₜ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₜrₜ
                  have h_1_lt : 1 < d + 1 := by omega
                  simp [EqMin.of.Lt h_lt_add_1, EqMod.of.Lt h_1_lt] at h_qₜ_div h_rₜ_mod
                  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₜrₜ]
                  rw [GetTranspose.eq.Get.fin]
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  simp [EqMin.of.Lt h_lt_add_1, EqMod.of.Lt h_1_lt]
                  apply congrArg
                  simp [h_z] at h_zq₀
                  simp [h_qr, h_zq₀, h_q'r']
                  have h_qₚrₚ := Eq_Sub.of.EqAdd.left h_qₚrₚ
                  rw [SubAdd.eq.AddSub.of.Ge] at h_qₚrₚ
                  ·
                    simp [h_qₚrₚ]
                    simp [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]
                    simp [Add_Add.eq.AddAdd, h_drop]
                    simp [h_qₚ_div]
                    left
                    rw [ProdDropTakePermute.eq.Get_0.of.GtLength (by omega)] at h_qₚ_div
                    simp [h_qₜ_div, h_rₜ_mod, h_qₚ_div]
                    rw [ProdDropTakePermute.eq.Get_0.of.GtLength (by omega)] at h_q'
                    simp [EqDivAddMul.of.Lt h_q', EqMod.of.Lt h_q']
                    left
                    rw [TakeTake.eq.Take.of.Ge (by omega)]
                    rw [TakePermute.eq.TailTake.of.GtLength (by omega)]
                  ·
                    simp [h_qₚ_div, h_drop]
                ·
                  simp [Rotate.eq.AppendDrop__Take]
              ·
                simp [Permute.eq.Append_AppendRotateTakeDrop]
            ·
              simp [Permute.eq.Append_AppendRotateTakeDrop]
          ·
            rw [MulProdS.eq.ProdAppend]
          ·
            rw [Rotate.eq.AppendDrop__Take]
        ·
          rw [MulProdS.eq.ProdAppend]
      ·
        rw [MulProdS.eq.ProdAppend]
        apply congrArg
        rw [Permute__Neg.eq.Append_AppendRotateDropTake] at h_permute
        simp at h_permute
        simpa [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]


-- created on 2025-10-19
-- updated on 2025-10-26
