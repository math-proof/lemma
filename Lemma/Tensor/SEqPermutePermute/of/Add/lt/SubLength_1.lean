import Lemma.List.TakeDropPermute.eq.TakeDrop.of.GtLength_Add
import Lemma.List.DropTakePermute.eq.ListGet.of.GtLength_Add
import Lemma.List.DropPermute.eq.Drop.of.GtLength_Add
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.ProdRotate.eq.MulProdS
import Lemma.List.TakeDropPermute.eq.Drop.of.Add.eq.SubLength_1
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.List.ProdDrop.eq.MulProdDrop_Add_1.of.Lt_Length
import Lemma.List.TakeRotate.eq.Drop.of.EqLength_Add
import Lemma.List.TakeDrop.eq.Drop.of.LeLength_Add
import Lemma.List.TailDrop.eq.Drop_Add_1
import Lemma.List.ProdRotate.eq.Prod
import Lemma.Nat.Add_AddMul.lt.Mul_Mul.of.Lt.Lt.Lt
import Lemma.List.DropPermute.eq.ListGet.of.Add.eq.SubLength_1
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.List.RotateRotate.eq.Rotate_Add
import Lemma.List.DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1
import Lemma.List.TakePermute.eq.Take
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.Add
import Lemma.Nat.LtVal
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.Nat.EqSubAdd
import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Nat.EqSub_Sub.of.Gt
import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.List.EqAppendTake__Drop
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.Nat.EqMin.of.Le
import Lemma.List.TakeTail.eq.TailTake
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.List.TakeDrop.eq.ListGet.of.Lt_Length
open List Nat Vector Tensor Bool
set_option maxHeartbeats 800000


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
  have h_length_permute := LengthPermute.eq.Length s (i := ⟨i, by omega⟩) (d := d)
  (X.permute ⟨i, by omega⟩ d).permute ⟨i + d, by rw [h_length_permute]; omega⟩ (-d) ≃ X := by
-- proof
  intro h_d h_length_permute
  have h_i_pos := NeZero.pos i
  rw [@Tensor.Permute.eq.Ite (i := ⟨i + d, by simp [LengthPermute.eq.Length]; omega⟩) (d := -d)]
  simp
  have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := i) (j := i + d) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  split_ifs with h_sub h_pos h_j_0 h_j_length
  repeat omega
  apply SEq.of.SEqDataS.Eq h_permute
  .
    simp
    let s' := (s.permute ⟨i, by grind⟩ d).take (i + d + 1)
    have h_permute_simp : (s'.take (s'.length - (1 - -(d : ℤ)).toNat) ++ (s'.drop (s'.length - (1 - -(d : ℤ)).toNat)).rotate ((1 - -(d : ℤ)).toNat ⊓ s'.length - 1)).prod * ((s.permute ⟨i, by grind⟩ d).drop (i + d + 1)).prod = s.prod := by
      simp only [s', h_toNat]
      rw [MulProdS.eq.ProdAppend]
      apply congrArg
      simp [h_length_permute]
      repeat rw [EqMin.of.Lt (by omega)]
      rw [Add.comm (a := 1), AddAdd.eq.Add_Add]
      repeat rw [EqSubAdd]
      rw [Add_Add.eq.AddAdd]
      have := Permute__Neg.eq.Append_AppendRotateTakeDrop (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by simp_all; grind⟩) (d := d)
      simp at this
      rwa [← this]
    apply SEqCast.of.SEq.Eq.Eq
    .
      rw [h_permute_simp, h_permute]
    .
      rw [h_permute]
    .
      apply SEq.of.All_EqGetS.Eq
      .
        intro t
        have h_t := LtVal t
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        have h_q := LtVal q
        have h_r := LtVal r
        -- have h_i : i < s.length := by omega
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
        unfold Tensor.permuteTail
        simp
        rw [GetCast.eq.Get.of.Eq.Lt]
        .
          simp only [ProdAppend.eq.MulProdS] at h_q
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
          simp [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
          unfold Tensor.rotate
          simp
          simp only [GetElem.getElem]
          have h_r' := LtVal r'
          rw [GetCast.eq.Get.of.Eq.Lt.fin]
          .
            simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r'
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
            rw [GetTranspose.eq.Get.fin]
            repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            rw [@Tensor.Permute.eq.Ite (i := ⟨i, by omega⟩) (d := d)]
            simp
            split_ifs with h_i_eq_0 h_d_eq_0 h_d_eq_0
            repeat omega
            simp
            have h_lt : (↑q' * (((s.permute ⟨i, by omega⟩ ↑d).take (i + d + 1)).drop ((i + d + 1) ⊓ (s.permute ⟨i, by omega⟩ ↑d).length - (1 + (d : ℤ)).toNat)).prod +
              (↑rₐ * (((s.permute ⟨i, by omega⟩ ↑d).take (i + d + 1)).drop ((i + d + 1) ⊓ (s.permute ⟨i, by omega⟩ ↑d).length - (1 + (d : ℤ)).toNat +
                ((1 + (d : ℤ)).toNat ⊓ ((i + d + 1) ⊓ (s.permute ⟨i, by omega⟩ ↑d).length) - 1) % ((i + d + 1) ⊓ (s.permute ⟨i, by omega⟩ ↑d).length - ((i + d + 1) ⊓ (s.permute ⟨i, by omega⟩ ↑d).length - (1 + (d : ℤ)).toNat)))).prod + ↑qₐ)) * ((s.permute ⟨i, by omega⟩ ↑d).drop (i + d + 1)).prod + ↑r <
              (s.take i).prod * (((s.drop i).take (d + 1)).rotate 1 ++ (s.drop i).drop (d + 1)).prod := by
              rw [MulProdS.eq.ProdAppend]
              rw [← Permute.eq.Append_AppendRotateTakeDrop (i := ⟨i, by omega⟩) (d := d)]
              rw [ProdPermute.eq.Prod]
              simp [h_length_permute]
              rw [EqMin.of.Lt (by omega)]
              have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatAdd.eq.Add 1 d
              rw [Add.comm (a := 1) (b := d)] at h_toNat
              rw [h_toNat]
              simp [AddAdd.eq.Add_Add]
              simp [Add_Add.eq.AddAdd (a := i)]
              simp [DropPermute.eq.Drop.of.GtLength_Add (i := ⟨i, by omega⟩) (show i + d < s.length by omega)]
              rw [List.DropTakePermute.eq.RotateTakeDrop.of.GtLength_Add (i := ⟨i, by omega⟩) (show i + d < s.length by omega)]
              rw [ProdRotate.eq.Prod]
              simp [DropTakePermute.eq.ListGet.of.GtLength_Add (i := ⟨i, by omega⟩) (show i + d < s.length by omega)]
              rw [Prod.eq.MulProdTake__ProdDrop s (i + d + 1)]
              apply AddMul.lt.Mul.of.Lt.Lt
              .
                rw [Prod.eq.MulProdTake__ProdDrop (s.take (i + d + 1)) i]
                rw [TakeTake.eq.Take.of.Ge (show i + d + 1 ≥ i by omega)]
                simp [AddAdd.eq.Add_Add (c := 1), ← List.TakeDrop.eq.DropTake]
                apply AddMul.lt.Mul.of.Lt.Lt
                .
                  have h_q' := LtVal q'
                  simp [h_length_permute, h_toNat] at h_q'
                  rw [EqMin.of.Lt (by omega)] at h_q'
                  simp [AddAdd.eq.Add_Add (c := 1)] at h_q'
                  rw [TakeTake.eq.Take.of.Ge (show i + (d + 1) ≥ i by omega)] at h_q'
                  rw [TakePermute.eq.Take (i := ⟨i, by omega⟩) (d := d)] at h_q'
                  exact h_q'
                .
                  rw [Prod.eq.MulProdDrop__ProdTake ((s.drop i).take (d + 1)) 1]
                  rw [TakeTake.eq.Take.of.Ge (by omega)]
                  rw [TakeDrop.eq.ListGet.of.Lt_Length (by omega)]
                  rw [TakeDrop.eq.DropTake s]
                  simp
                  apply AddMul.lt.Mul.of.Lt.Lt
                  .
                    have h_rₐ := LtVal rₐ
                    simp [h_length_permute, h_toNat] at h_rₐ
                    rw [EqMin.of.Le (show i + d + 1 ≤ s.length by omega)] at h_rₐ
                    rw [EqSub_Sub.of.Gt (by omega)] at h_rₐ
                    simp [AddAdd.eq.Add_Add (c := 1)] at h_rₐ
                    rw [← TakeDrop.eq.DropTake] at h_rₐ
                    rw [TakeTake.eq.Take.of.Ge (show d + 1 ≥ d by omega)] at h_rₐ
                    simp [Add.comm (b := 1), Add_Add.eq.AddAdd]
                    simp [← TakeDrop.eq.DropTake]
                    rw [Add.comm (a := 1)]
                    rw [List.TakeDropPermute.eq.TakeDrop.of.GtLength_Add (i := ⟨i, by omega⟩) (show i + d < s.length by omega)] at h_rₐ
                    simp at h_rₐ
                    exact h_rₐ
                  .
                    have h_qₐ := LtVal qₐ
                    simp [h_length_permute, h_toNat] at h_qₐ
                    rw [EqMin.of.Le (show i + d + 1 ≤ s.length by omega)] at h_qₐ
                    rw [EqSub_Sub.of.Gt (by omega)] at h_qₐ
                    simp [AddAdd.eq.Add_Add (c := 1)] at h_qₐ
                    rw [Add_Add.eq.AddAdd (c := 1)] at h_qₐ
                    rw [List.DropTakePermute.eq.ListGet.of.GtLength_Add (i := ⟨i, by omega⟩) (show i + d < s.length by omega)] at h_qₐ
                    simp at h_qₐ
                    exact h_qₐ
              .
                simp [List.DropPermute.eq.Drop.of.GtLength_Add (i := ⟨i, by omega⟩) (show i + d < s.length by omega)] at h_r
                exact h_r
            rw [GetCast.eq.Get.of.Eq.Lt.fin]
            .
              let ⟨qₜ, rₜ, h_qₜrₜ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₜrₜ]
              unfold Tensor.permuteHead
              simp
              have h_rₜ := LtVal rₜ
              simp only [ProdAppend.eq.MulProdS] at h_rₜ
              rw [GetCast.eq.Get.of.Eq.Lt.fin]
              .
                let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_rₜ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
                unfold Tensor.rotate
                simp
                have h_qₑ := LtVal qₑ
                simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₑ
                rw [GetCast.eq.Get.of.Eq.Lt.fin]
                .
                  let ⟨qₓ, rₓ, h_qₓrₓ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₑ
                  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₓrₓ]
                  rw [GetTranspose.eq.Get.fin]
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  apply congrArg
                  sorry
                .
                  exact h_qₑ
                .
                  rw [MulProdS.eq.ProdAppend]
                  rw [Rotate.eq.AppendDrop__Take]
              .
                exact h_rₜ
              .
                rw [MulProdS.eq.ProdAppend]
            .
              exact h_lt
            .
              rw [MulProdS.eq.ProdAppend]
              rw [Permute.eq.Append_AppendRotateTakeDrop]
          .
            convert h_r'
            simp [Rotate.eq.AppendDrop__Take]
          .
            simp [Rotate.eq.AppendDrop__Take]
        .
          rwa [MulProdS.eq.ProdAppend]
        .
          rw [MulProdS.eq.ProdAppend]
      .
        rw [h_permute_simp]


-- created on 2025-10-19
