import Lemma.List.TakePermute.eq.TailTake.of.Lt_Length
import Lemma.List.ProdDropTakePermute.eq.Get_0.of.Lt_Length
import Lemma.Nat.EqDivAddMul.of.Lt
import Lemma.List.DropPermute.eq.Drop.of.Lt_Length
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.Nat.LtAddMulAddMul.of.Lt.Lt.Lt.Eq
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.Add
import Lemma.Nat.LtVal
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.SubAdd.eq.AddSub.of.Le
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
open List Nat Vector Tensor Bool
set_option maxHeartbeats 300000


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d < s.length - 1)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨0, by grind⟩ d).permute ⟨d, by simp [LengthPermute.eq.Length]; omega⟩ (-d) ≃ X := by
-- proof
  have h_d := NeZero.pos d
  rw [@Tensor.Permute.eq.Ite (i := ⟨d, by simp [LengthPermute.eq.Length]; omega⟩) (d := -d)]
  simp
  split_ifs with h_sub h_pos h_eq_d
  repeat omega
  ·
    simp at h_eq_d
    rw [LengthPermute.eq.Length] at h_eq_d
    omega
  ·
    have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := 0) (j := d) ⟨by omega, by omega⟩
    simp at h_permute
    have h_lt_add_1 := LtAdd.of.Lt_Sub h
    apply SEq.of.SEqDataS.Eq
    ·
      rw [h_permute]
    ·
      have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
      simp
      apply SEqCast.of.SEq.Eq.Eq
      ·
        rw [MulProdS.eq.ProdAppend]
        rw [h_toNat]
        simp [LengthPermute.eq.Length]
        rw [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]
        simp [Permute__Neg.eq.Append_AppendRotateTakeDrop]
      ·
        rw [h_permute]
      ·
        rw [h_toNat]
        unfold Tensor.permuteTail
        simp
        apply SEq.of.All_EqGetS.Eq
        ·
          have h_drop := DropPermute.eq.Drop.of.Lt_Length (show d < s.length by omega)
          intro t
          have h_t := LtVal t
          let ⟨k', k, h_k'k⟩ := Any_EqAddMul.of.Lt_Mul h_t
          have h_k := LtVal k
          have h_k' := LtVal k'
          simp [GetFlatten.eq.Get.of.Eq_AddMul h_k'k.symm]
          rw [GetCast.eq.Get.of.Eq.Lt]
          ·
            simp only [ProdAppend.eq.MulProdS] at h_k'
            let ⟨z, k'', h_zk''⟩ := Any_EqAddMul.of.Lt_Mul h_k'
            have h_z := LtVal z
            simp [LengthPermute.eq.Length, EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)] at h_z
            have h_k'' := LtVal k''
            rw [GetFlatten.eq.Get.of.Eq_AddMul h_zk''.symm]
            simp
            unfold Tensor.rotate
            simp only [GetElem.getElem]
            repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
            ·
              simp only [Rotate.eq.AppendDrop__Take] at h_k''
              rw [ProdAppend.eq.MulProdS] at h_k''
              let ⟨i, j, h_ij⟩ := Any_EqAddMul.of.Lt_Mul h_k''
              simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_ij.symm]
              rw [GetTranspose.eq.Get.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              rw [@Tensor.Permute.eq.Ite (i := ⟨0, by omega⟩) (d := d)]
              simp
              split_ifs
              unfold Tensor.permuteHead
              simp
              rw [DataCast.eq.Cast_Data.of.Eq]
              ·
                simp [h_z]
                have h_j := LtVal j
                have h_i := LtVal i
                simp [LengthPermute.eq.Length] at h_j h_i
                simp [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)] at h_j h_i
                have h_permute := Permute.eq.AppendRotateTake___Drop.of.EqVal_0 (s := s) (i := ⟨0, by omega⟩) (by simp) d
                rw [GetCast.eq.Get.of.Eq.Lt.fin]
                ·
                  unfold Tensor.rotate
                  simp [LengthPermute.eq.Length]
                  simp [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]
                  have h_lt : (j * (((s.permute ⟨0, by grind⟩ d).take (d + 1)).drop d).prod + i) * ((s.permute ⟨0, by grind⟩ d).drop (d + 1)).prod + k < ((s.take (d + 1)).rotate 1).prod * (s.drop (d + 1)).prod :=
                    LtAddMulAddMul.of.Lt.Lt.Lt.Eq (by simp [h_permute]) h_j h_i h_k
                  let ⟨i', j', h_i'j'⟩ := Any_EqAddMul.of.Lt_Mul h_lt
                  let ⟨h_i'_div, h_j'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_i'j'.symm
                  simp [h_drop] at h_i'_div
                  rw [EqDivAddMul.of.Lt (by aesop)] at h_i'_div
                  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_i'j'.symm]
                  have h_i' := LtVal i'
                  rw [GetCast.eq.Get.of.Eq.Lt.fin]
                  ·
                    simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_i'
                    let ⟨i'', j'', h_i''j''⟩ := Any_EqAddMul.of.Lt_Mul h_i'
                    let ⟨h_i''_div, h_j''_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_i''j''.symm
                    have h_1_lt : 1 < d + 1 := by omega
                    simp [EqMin.of.Lt h_lt_add_1, EqMod.of.Lt h_1_lt] at h_i''_div h_j''_mod
                    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_i''j''.symm]
                    rw [GetTranspose.eq.Get.fin]
                    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    simp [EqMin.of.Lt h_lt_add_1, EqMod.of.Lt h_1_lt] at h_i''j'' ⊢
                    apply congrArg
                    simp [h_z] at h_zk''
                    simp [← h_k'k, ← h_zk'', ← h_ij]
                    have h_i'j' := Eq_Sub.of.EqAdd.left h_i'j'.symm
                    rw [SubAdd.eq.AddSub.of.Le] at h_i'j'
                    ·
                      simp [h_i'j']
                      simp [LengthPermute.eq.Length]
                      simp [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]
                      simp [Add_Add.eq.AddAdd, h_drop]
                      simp [h_i'_div]
                      left
                      rw [ProdDropTakePermute.eq.Get_0.of.Lt_Length (by omega)] at h_i'_div
                      simp [h_i''_div, h_j''_mod, h_i'_div]
                      rw [ProdDropTakePermute.eq.Get_0.of.Lt_Length (by omega)] at h_i
                      simp [EqDivAddMul.of.Lt h_i, EqMod.of.Lt h_i]
                      left
                      rw [TakeTake.eq.Take.of.Ge (by omega)]
                      rw [TakePermute.eq.TailTake.of.Lt_Length (by omega)]
                    ·
                      simp [h_i'_div, h_drop]
                  ·
                    rw [MulProdS.eq.ProdAppend]
                    convert h_i'
                    simp [Rotate.eq.AppendDrop__Take]
                  ·
                    simp [Rotate.eq.AppendDrop__Take]
                ·
                  simp [LengthPermute.eq.Length]
                  simp [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]
                  apply LtAddMulAddMul.of.Lt.Lt.Lt.Eq _ h_j h_i h_k
                  repeat rw [MulProdS.eq.ProdAppend]
                  simp [h_permute]
                ·
                  simp [Permute.eq.Append_AppendRotateTakeDrop]
              ·
                simp [Permute.eq.Append_AppendRotateTakeDrop]
            ·
              rw [MulProdS.eq.ProdAppend]
              rwa [AppendDrop__Take.eq.Rotate]
            ·
              rw [MulProdS.eq.ProdAppend]
            ·
              rwa [AppendDrop__Take.eq.Rotate]
            ·
              rw [Rotate.eq.AppendDrop__Take]
          ·
            rwa [MulProdS.eq.ProdAppend]
          ·
            rw [MulProdS.eq.ProdAppend]
        ·
          rw [MulProdS.eq.ProdAppend]
          apply congrArg
          simp [LengthPermute.eq.Length]
          rw [Permute__Neg.eq.Append_AppendRotateTakeDrop] at h_permute
          simp at h_permute
          simpa [EqMin.of.Lt h_lt_add_1, Add.comm (a := 1)]


-- created on 2025-10-19
-- updated on 2025-10-22
