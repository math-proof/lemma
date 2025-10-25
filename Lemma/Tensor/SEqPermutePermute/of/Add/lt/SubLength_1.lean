import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.List.TakeDropTakePermute.eq.TakeDrop.of.GtLength_Add
import Lemma.Nat.MulMul
import Lemma.List.ProdTakeDrop.eq.Get.of.Lt_Length
import Lemma.List.ProdTakeDrop.eq.MulProdTakeDrop.of.Lt_Length
import Lemma.Nat.DivDiv.eq.Div_Mul
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
private lemma main'
  [NeZero (d : ℕ)]
  [NeZero (i : ℕ)]
  {s : List ℕ}
-- given
  (h : i + d < s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  have h_i : i < s.length := by omega
  have h_length_permute := LengthPermute.eq.Length s (i := ⟨i, h_i⟩) (d := d)
  (X.permute ⟨i, h_i⟩ d).permute ⟨i + d, by rw [h_length_permute]; omega⟩ (-d) ≃ X := by
-- proof
  intro h_d h_i h_length_permute
  have h_i_pos := NeZero.pos i
  rw [@Tensor.Permute.eq.Ite (i := ⟨i + d, by simp [LengthPermute.eq.Length]; omega⟩) (d := -d)]
  simp
  have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := i) (j := i + d) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  have h_toNatSub := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  split_ifs with h_sub h_pos h_j_0 h_j_length
  repeat omega
  apply SEq.of.SEqDataS.Eq h_permute
  .
    simp
    let s' := (s.permute ⟨i, by grind⟩ d).take (i + d + 1)
    have h_permute_simp : (s'.take (s'.length - (1 - -(d : ℤ)).toNat) ++ (s'.drop (s'.length - (1 - -(d : ℤ)).toNat)).rotate ((1 - -(d : ℤ)).toNat ⊓ s'.length - 1)).prod * ((s.permute ⟨i, by grind⟩ d).drop (i + d + 1)).prod = s.prod := by
      simp only [s', h_toNatSub]
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
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
        unfold Tensor.permuteTail
        simp
        rw [GetCast.eq.Get.of.Eq.Lt]
        .
          simp only [ProdAppend.eq.MulProdS] at h_q
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
          let ⟨h_q'_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
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
            rw [@Tensor.Permute.eq.Ite (i := ⟨i, h_i⟩) (d := d)]
            simp
            split_ifs with h_i_eq_0 h_d_eq_0 h_d_eq_0
            repeat omega
            simp
            have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatAdd.eq.Add 1 d
            rw [Add.comm (a := 1) (b := d)] at h_toNat
            have h_qₐ := LtVal qₐ
            have h_rₐ := LtVal rₐ
            simp [h_length_permute, h_toNat] at h_qₐ h_rₐ
            have h_Leid : i + d + 1 ≤ s.length := by omega
            rw [EqMin.of.Le h_Leid] at h_qₐ h_rₐ
            rw [EqSub_Sub.of.Gt (by omega)] at h_qₐ h_rₐ
            simp [AddAdd.eq.Add_Add (c := 1)] at h_qₐ h_rₐ
            rw [Add_Add.eq.AddAdd (c := 1)] at h_qₐ
            have h_Ltid : i + d < s.length := by omega
            rw [List.DropTakePermute.eq.ListGet.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_qₐ
            simp at h_qₐ
            rw [← TakeDrop.eq.DropTake] at h_rₐ
            rw [TakeTake.eq.Take.of.Ge (show d + 1 ≥ d by omega)] at h_rₐ
            rw [List.TakeDropPermute.eq.TakeDrop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_rₐ
            simp at h_rₐ
            simp [List.DropPermute.eq.Drop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_r
            let s' := s.permute ⟨i, h_i⟩ d
            have h_lt : (q' * ((s'.take (i + d + 1)).drop ((i + d + 1) ⊓ s'.length - (1 + (d : ℤ)).toNat)).prod + (rₐ * ((s'.take (i + d + 1)).drop ((i + d + 1) ⊓ s'.length - (1 + (d : ℤ)).toNat + ((1 + (d : ℤ)).toNat ⊓ ((i + d + 1) ⊓ s'.length) - 1) % ((i + d + 1) ⊓ s'.length - ((i + d + 1) ⊓ s'.length - (1 + (d : ℤ)).toNat)))).prod + qₐ)) * (s'.drop (i + d + 1)).prod + r < (s.take i).prod * (((s.drop i).take (d + 1)).rotate 1 ++ (s.drop i).drop (d + 1)).prod := by
              simp only [s']
              rw [MulProdS.eq.ProdAppend]
              rw [← Permute.eq.Append_AppendRotateTakeDrop (i := ⟨i, h_i⟩) (d := d)]
              rw [ProdPermute.eq.Prod]
              simp [h_length_permute]
              rw [EqMin.of.Lt (by omega)]
              rw [h_toNat]
              simp [AddAdd.eq.Add_Add]
              simp [Add_Add.eq.AddAdd (a := i)]
              simp [DropPermute.eq.Drop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid]
              rw [List.DropTakePermute.eq.RotateTakeDrop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid]
              rw [ProdRotate.eq.Prod]
              simp [DropTakePermute.eq.ListGet.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid]
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
                  rw [TakePermute.eq.Take (i := ⟨i, h_i⟩) (d := d)] at h_q'
                  exact h_q'
                .
                  rw [Prod.eq.MulProdDrop__ProdTake ((s.drop i).take (d + 1)) 1]
                  rw [TakeTake.eq.Take.of.Ge (by omega)]
                  rw [TakeDrop.eq.ListGet.of.Lt_Length (by omega)]
                  rw [TakeDrop.eq.DropTake s]
                  simp
                  apply AddMul.lt.Mul.of.Lt.Lt
                  .
                    simp [Add.comm (b := 1), Add_Add.eq.AddAdd]
                    simp [← TakeDrop.eq.DropTake]
                    rw [Add.comm (a := 1)]
                    exact h_rₐ
                  .
                    exact h_qₐ
              .
                exact h_r
            rw [GetCast.eq.Get.of.Eq.Lt.fin]
            .
              simp only [s'] at h_lt
              let ⟨qₜ, rₜ, h_qₜrₜ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              let ⟨h_qₜ_div, h_rₜ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₜrₜ
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₜrₜ]
              unfold Tensor.permuteHead
              simp
              have h_rₜ := LtVal rₜ
              simp only [ProdAppend.eq.MulProdS] at h_rₜ
              rw [GetCast.eq.Get.of.Eq.Lt.fin]
              .
                let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_rₜ
                let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
                unfold Tensor.rotate
                simp
                have h_qₑ := LtVal qₑ
                simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₑ
                rw [GetCast.eq.Get.of.Eq.Lt.fin]
                .
                  let ⟨qₓ, rₓ, h_qₓrₓ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₑ
                  let ⟨h_qₓ_div, h_rₓ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₓrₓ
                  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₓrₓ]
                  rw [GetTranspose.eq.Get.fin]
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  apply congrArg
                  simp [EqMin.of.Le (show d + 1 ≤ s.length - i by omega)]
                  rw [EqMod.of.Lt (show 1 < d + 1 by omega)]
                  simp [TakeDrop.eq.DropTake s]
                  simp [h_qr]
                  simp [DropPermute.eq.Drop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid]
                  simp [h_length_permute, h_toNat] at h_qₜ_div
                  simp [EqMin.of.Le h_Leid] at h_qₜ_div
                  simp [AddAdd.eq.Add_Add (c := 1)] at h_qₜ_div
                  simp [Add_Add.eq.AddAdd (a := i)] at h_qₜ_div
                  simp [DropTakePermute.eq.RotateTakeDrop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_qₜ_div
                  rw [ProdRotate.eq.Prod] at h_qₜ_div
                  simp [DropTakePermute.eq.ListGet.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_qₜ_div
                  simp [DropPermute.eq.Drop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_qₜ_div
                  rw [Div_Mul.eq.DivDiv.comm] at h_qₜ_div
                  rw [DivAddMul.eq.Add_Div.of.Gt_0] at h_qₜ_div
                  .
                    simp [Div.eq.Zero.of.Lt h_r] at h_qₜ_div
                    rw [DivAddMul.eq.Add_Div.of.Gt_0] at h_qₜ_div
                    .
                      have h_lt := Nat.AddMul.lt.Mul.of.Lt.Lt h_rₐ h_qₐ
                      rw [MulProdTakeDrop.eq.ProdTakeDrop.of.Lt_Length (by omega)] at h_lt
                      simp [Div.eq.Zero.of.Lt h_lt] at h_qₜ_div
                      simp [h_qₜ_div]
                      simp [h_length_permute, h_toNat] at h_q'_div
                      simp [EqMin.of.Le h_Leid] at h_q'_div
                      simp [List.DropTakePermute.eq.RotateTakeDrop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_q'_div
                      simp [ProdRotate.eq.Prod] at h_q'_div
                      simp [Add.comm (a := d), Add_Add.eq.AddAdd]
                      simp [DropTake.eq.TakeDrop]
                      simp [h_rₑ_mod]
                      simp [h_length_permute, h_toNat] at h_rₜ_mod
                      simp [EqMin.of.Le h_Leid] at h_rₜ_mod
                      simp [List.DropTakePermute.eq.RotateTakeDrop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_rₜ_mod
                      simp [AddAdd.eq.Add_Add (c := 1)] at h_rₜ_mod
                      simp [Add_Add.eq.AddAdd (a := i)] at h_rₜ_mod
                      simp [ProdRotate.eq.Prod] at h_rₜ_mod
                      simp [DropTakePermute.eq.ListGet.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_rₜ_mod
                      simp [DropPermute.eq.Drop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_rₜ_mod
                      rw [MulAdd.eq.AddMulS] at h_rₜ_mod
                      simp [MulMul.eq.Mul_Mul, AddAdd.eq.Add_Add] at h_rₜ_mod
                      simp [h_rₜ_mod]
                      simp [Add_Add.eq.AddAdd, EqMod.of.Lt h_r]
                      simp [EqMin.of.Le (show d + 1 ≤ s.length - i by omega)] at h_qₓ_div h_rₓ_mod
                      rw [EqMod.of.Lt (show 1 < d + 1 by omega)] at h_qₓ_div h_rₓ_mod
                      simp [TakeTake.eq.Take.of.Ge (show d + 1 ≥ 1 by omega)] at h_qₓ_div h_rₓ_mod
                      simp [ProdTakeDrop.eq.Get.of.Lt_Length h_i] at h_qₓ_div h_rₓ_mod
                      simp [h_qₑ_div] at h_qₓ_div h_rₓ_mod
                      simp [Add_Add.eq.AddAdd] at h_qₓ_div h_rₓ_mod
                      simp [AddAdd.comm]
                      simp [h_qₓ_div, h_rₓ_mod]
                      simp [Add_Add.eq.AddAdd] at h_rₜ_mod
                      have h_lt := Nat.AddMul.lt.Mul.of.Lt.Lt h_lt h_r
                      rw [EqMod.of.Lt h_lt] at h_rₜ_mod
                      simp [h_rₜ_mod]
                      rw [Nat.DivAddMul.eq.Add_Div.of.Gt_0 (by omega)]
                      simp [Div.eq.Zero.of.Lt h_r]
                      rw [Nat.DivAddMul.eq.Add_Div.of.Gt_0 (by omega)]
                      simp [EqMod.of.Lt h_qₐ, Div.eq.Zero.of.Lt h_qₐ]
                      simp [h_length_permute, h_toNat] at h_qₐrₐ
                      simp [EqMin.of.Le h_Leid] at h_qₐrₐ
                      simp [show i + d + 1 - i = d + 1 by omega] at h_qₐrₐ
                      rw [TakeDropTakePermute.eq.TakeDrop.of.GtLength_Add (i := ⟨i, h_i⟩) (by simp; omega)] at h_qₐrₐ
                      simp [← h_qₐrₐ]
                      rw [ProdDrop.eq.MulProdS s i (d + 1)]
                      rw [Mul_Mul.eq.MulMul]
                      rw [Add_Add.eq.AddAdd]
                      simp [AddMulS.eq.MulAdd]
                      left
                      simp [h_length_permute, h_toNat] at h_q'r'
                      simp [EqMin.of.Le h_Leid] at h_q'r'
                      simp [DropTakePermute.eq.RotateTakeDrop.of.GtLength_Add (i := ⟨i, h_i⟩) h_Ltid] at h_q'r'
                      simp [ProdRotate.eq.Prod] at h_q'r'
                      rw [h_q'r']
                    .
                      have h_qₑ := LtVal qₑ
                      simp [ProdRotate.eq.Prod] at h_qₑ
                      grind
                  .
                    have h_rₑ := LtVal rₑ
                    simp at h_rₑ
                    grind
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


@[main]
private lemma reverse
  [NeZero (d : ℕ)]
  [NeZero (i : ℕ)]
  {s : List ℕ}
-- given
  (h : i + d < s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  have h_i : i + d < s.length := by omega
  have h_length_permute := LengthPermute.eq.Length s (i := ⟨i + d, h_i⟩) (d := -d)
  (X.permute ⟨i + d, h_i⟩ (-d)).permute ⟨i, by rw [h_length_permute]; omega⟩ d ≃ X := by
-- proof
  intro h_d h_i h_length_permute
  have h_i_pos := NeZero.pos i
  rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp [LengthPermute.eq.Length]; omega⟩) (d := d)]
  simp
  have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := i) (j := i + d) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  have h_toNatSub := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  split_ifs with h_sub h_pos
  repeat omega
  apply SEq.of.SEqDataS.Eq
  .
    sorry
  .
    sorry


-- created on 2025-10-19
