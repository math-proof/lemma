import Lemma.List.EqPermutePermute__Neg.of.In_Ioo_Length
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.DropPermute.eq.Drop.of.Lt_Length
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDropTakePermute.eq.Get_0.of.Lt_Length
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TakePermute.eq.TailTake.of.Lt_Length
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqDivAddMul.of.Lt
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Nat.LtAddMulAddMul.of.Lt.Lt.Lt.Eq
import Lemma.Nat.LtVal
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.SubAdd.eq.AddSub.of.Le
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Nat Vector Tensor Bool
set_option maxHeartbeats 400000


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d < s.length - 1)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨d, by grind⟩ (-d)).permute ⟨0, by simp; omega⟩ d ≃ X := by
-- proof
  have h_d := NeZero.pos d
  rw [@Tensor.Permute.eq.Ite (i := ⟨0, by simp; omega⟩) (d := d)]
  simp
  split_ifs with h_sub
  ·
    omega
  ·
    have h_permute := EqPermutePermute__Neg.of.In_Ioo_Length (s := s) (i := d) (j := 0) ⟨by omega, by omega⟩
    simp at h_permute
    have h_lt_add_1 := LtAdd.of.Lt_Sub h
    apply SEqCast.of.SEq.Eq.Eq
    .
      simp [Permute.eq.Append_AppendRotateTakeDrop]
    .
      rw [h_permute]
    .
      unfold Tensor.permuteHead
      simp
      apply SEq.of.SEqDataS.Eq
      .
        rw [← List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (by simp; omega), h_permute]
      .
        simp
        apply SEqCast.of.SEq.Eq.Eq
        .
          rw [MulProdS.eq.ProdAppend]
        .
          rw [← List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (by simp; omega), h_permute]
        .
          apply SEq.of.All_EqGetS.Eq
          .
            intro t
            have h_t := LtVal t
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
            have h_q := LtVal q
            simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q
            have h_r := LtVal r
            simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
            unfold Tensor.rotate
            simp only [GetElem.getElem]
            repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
            .
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              rw [GetTranspose.eq.Get.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              rw [@Tensor.Permute.eq.Ite (i := ⟨d, by omega⟩) (d := -d)]
              simp
              split_ifs with h_sub' h_pos'
              repeat omega
              simp
              have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
              rw [Add.comm] at h_toNat
              have h_1_lt : 1 < d + 1 := by omega
              rw [GetCast.eq.Get.of.Eq.Lt.fin]
              .
                sorry
              .
                rw [h_toNat]
                simp [EqMin.of.Lt h_lt_add_1]
                rw [EqMod.of.Lt h_1_lt]
                sorry
              .
                rw [h_toNat]
                rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
                simp [EqMin.of.Lt h_lt_add_1]
            .
              exact h_q
            .
              rw [MulProdS.eq.ProdAppend]
            .
              rwa [ProdAppend.eq.MulProdS]
            .
              rw [Rotate.eq.AppendDrop__Take]
          .
            rw [MulProdS.eq.ProdAppend]
            rw [← List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (by simp; omega), h_permute]


-- created on 2025-10-26
