import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.DropPermute__Neg.eq.Drop
import Lemma.List.EqPermutePermute__Neg.of.In_Ioo_Length
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.Append_RotateDropTake.of.EqLength_Add_1
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailTakeDrop.eq.TakeDrop
import Lemma.List.TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSubAdd
import Lemma.Nat.LtVal
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Bool Nat Tensor Vector
set_option maxHeartbeats 800000


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
  split_ifs with h_sub h_pos
  repeat omega
  have h_permute := EqPermutePermute__Neg.of.In_Ioo_Length (s := s) (i := i + d) (j := i) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  apply SEq.of.SEqDataS.Eq
  ·
    exact h_permute
  ·
    simp
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
          rw [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
          unfold Tensor.rotate
          simp [GetElem.getElem]
          have h_q' := LtVal q'
          simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q'
          rw [GetCast.eq.Get.of.Eq.Lt.fin h_q']
          ·
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q'
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
            rw [GetTranspose.eq.Get.fin]
            repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            rw [@Tensor.Permute.eq.Ite (i := ⟨i + d, by omega⟩) (d := -d)]
            simp
            split_ifs with h_sub' h_neg
            repeat omega
            have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
            rw [Add.comm] at h_toNat
            unfold Tensor.permuteTail
            simp
            rw [DataCast.eq.Cast_Data.of.Eq]
            ·
              simp
              have h_length_eq_add_1 : s.length = i + d + 1 := by omega
              rw [GetCast.eq.Get.of.Eq.Lt.fin]
              ·
                sorry
              ·
                rw [h_toNat]
                simp [← h_i_eq]
                rw [EqMin.of.Le (by omega), EqMod.of.Lt (show 1 < d + 1 by omega)]
                rw [EqMin.of.Lt (by omega), EqSubAdd]
                rw [Add_Add.eq.AddAdd (a := i)]
                rw [DropPermute__Neg.eq.Drop ⟨i + d, by grind⟩]
                simp [← h_length_eq_add_1]
                simp [TailTakeDrop.eq.TakeDrop]
                rw [TakeDropPermute__Neg.eq.TakeDrop.of.GtLength_Add (by omega)]
                sorry
              ·
                rw [h_toNat]
                rw [MulProdS.eq.ProdAppend]
                rw [EqMin.of.Lt (by omega), EqSubAdd]
                simp [← h_i_eq]
                rw [MulProdS.eq.ProdAppend]
                apply congrArg
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
-- updated on 2025-10-27
