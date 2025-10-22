import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
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
import Lemma.Nat.EqSubAdd
import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
open List Tensor Bool Nat Vector


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
  (X.permute ⟨i, by omega⟩ d).permute ⟨i + d, by simp [LengthPermute.eq.Length]; omega⟩ (-d) ≃ X := by
-- proof
  intro h_d
  rw [@Tensor.Permute.eq.Ite (i := ⟨i + d, by simp [LengthPermute.eq.Length]; omega⟩) (d := -d)]
  simp
  split_ifs with h_sub h_pos h_j_0 h_eq_d
  repeat omega
  ·
    have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := i) (j := i + d) ⟨by omega, by omega⟩
    simp at h_permute
    rw [EqSubAdd.left] at h_permute
    have h_i := NeZero.pos i
    have h_lt_add_1 : 1 + d < s.length := by omega
    have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
    apply SEqCast.of.SEq.Eq.Eq
    ·
      rw [h_toNat]
      simp [LengthPermute.eq.Length]
      simp [EqMin.of.Lt h_lt_add_1]
      simp [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by grind⟩) (by omega)]
      simp [LengthPermute.eq.Length]
      simp [Add.comm (a := d), EqMin.of.Lt h_lt_add_1]
    ·
      rw [h_permute]
    ·
      rw [h_toNat]
      unfold Tensor.permuteTail
      simp
      apply SEq.of.SEqDataS.Eq
      .
        simp [Add.comm (a := 1)]
        simp [← Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by grind⟩) (by omega)]
        simp [h_permute]
      .
        apply SEq.of.All_EqGetS.Eq
        .
          intro t
          have h_t := LtVal t
          simp only [ProdAppend.eq.MulProdS] at h_t
          let ⟨q, r, h_qr⟩ := Any_EqAddMul.of.Lt_Mul h_t
          have h_q := LtVal q
          have h_r := LtVal r
          sorry
        .
          simp [Add.comm (a := 1)]
          rw [MulProdS.eq.ProdAppend]
          simp [← Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by grind⟩) (by omega)]
          simp [h_permute]
  ·
    simp at h_eq_d
    rw [LengthPermute.eq.Length] at h_eq_d
    contradiction


-- created on 2025-10-19
-- updated on 2025-10-22
