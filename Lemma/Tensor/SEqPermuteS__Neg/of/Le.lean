import Lemma.Tensor.SEqPermuteTail.of.Le_1
import Lemma.Tensor.SEqPermuteTailS.of.Ge_Length
import Lemma.Tensor.SEqPermuteTailS.of.SEq.Eq
import Lemma.List.EqPermuteS.of.Le
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.EqPermute__0
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute.eq.Ite
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add_1.ge.Mod1
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Eq.of.Sub.eq.Zero.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtVal
import Lemma.Nat.SubSub
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqPermuteHeadS.of.Ge_Length
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Tensor.SEqPermuteTail_1
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Tensor Bool List Vector
set_option maxHeartbeats 400000


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≤ d)
  (X : Tensor α s) :
-- imply
  X.permute i (-d) ≃ X.permute i (-i) := by
-- proof
  by_cases h_d : i = d
  .
    subst h_d
    rfl
  .
    have h_d := Gt.of.Ge.Ne h (by omega)
    rw [@Tensor.Permute.eq.Ite]
    simp
    have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
    split_ifs with h_i0 h_pos? h_i h_length
    repeat omega
    apply SEqCast.of.SEq.Eq
    .
      rw [h_toNat]
      rw [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
      simp [h_length]
      simp [show (s.length - (1 + d)) = 0 by omega]
      simp [show (s.length - 1 + 1) = s.length by omega]
      simp [show (s.length - 1 - d) = 0 by omega]
      apply congrArg
      omega
    .
      rw [h_toNat]
      have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 i
      simp [@Tensor.Permute.eq.Ite]
      split_ifs with h_i0 h_pos
      .
        apply SEq_Cast.of.SEq.Eq
        .
          simp [h_i0]
          rw [List.EqPermute__0]
        .
          have := Tensor.SEqPermuteTailS.of.Ge_Length (n := 1 + d) (by omega) X
          apply SEq.trans this
          apply Tensor.SEqPermuteTail.of.Le_1
          omega
      .
        omega
      .
        apply SEq_Cast.of.SEq.Eq
        .
          rw [h_toNat]
          rw [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
          simp [h_length]
          simp [show (s.length - (1 + (s.length - 1))) = 0 by omega]
          simp [show (s.length - 1 + 1) = s.length by omega]
          apply congrArg
          omega
        .
          rw [h_toNat]
          rw [h_length]
          rw [show (1 + (s.length - 1)) = s.length by omega]
          apply Tensor.SEqPermuteTailS.of.Ge_Length
          omega
    .
      apply SEq.of.SEqDataS.Eq
      .
        apply List.EqPermuteS.of.Le
        omega
      .
        simp
        apply SEqCast.of.SEq.Eq
        .
          rw [h_toNat]
          rw [MulProdS.eq.ProdAppend]
          rw [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
          rw [EqMin.of.Ge (by simp; omega)]
          simp [EqMin.of.Le (show i + 1 ≤ s.length by omega)]
          simp [show i + 1 - (1 + d) = i - d by omega]
          left
          left
          rw [EqMin.of.Ge (by omega)]
        .
          rw [h_toNat]
          apply SEq.of.All_EqGetS.Eq
          .
            intro t
            have h_t := LtVal t
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
            let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
            have h_r := LtVal r
            simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
            simp [@Tensor.Permute.eq.Ite]
            split_ifs with h_d0 h_pos
            .
              sorry
            .
              omega
            .
              sorry
          .
            rw [MulProdS.eq.ProdAppend]
            apply congrArg
            simp [show (↑i + 1) ⊓ s.length = ↑i + 1 by omega]
            simp [show (↑i + 1 - (1 + d)) = ↑i - d by omega]
            simp [show (1 + d) ⊓ (↑i + 1) = i + 1 by omega]
            simp [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
            simp [show (↑i - d) = 0 by omega]


-- created on 2025-10-30
