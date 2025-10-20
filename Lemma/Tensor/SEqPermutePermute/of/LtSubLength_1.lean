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
import Lemma.Nat.ToNatAdd.eq.Add
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
open List Tensor Bool Nat Vector


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
  rw [Permute.eq.Ite (d := ⟨d, by simp [LengthPermute.eq.Length]; omega⟩) (k := -d)]
  simp
  split_ifs with h_sub h_pos h_eq_d
  repeat omega
  .
    simp at h_eq_d
    rw [LengthPermute.eq.Length] at h_eq_d
    omega
  .
    have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := 0) (j := d) ⟨by omega, by omega⟩
    simp at h_permute
    apply SEq.of.SEqDataS.Eq
    .
      rw [h_permute]
    .
      have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
      simp
      apply SEqCast.of.SEq.Eq.Eq
      .
        rw [MulProdS.eq.ProdAppend]
        apply congrArg
        rw [h_toNat]
        simp [LengthPermute.eq.Length]
        rw [EqMin.of.Lt (by omega), Add.comm (a := 1)]
        simp [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
      .
        apply congrArg
        rw [h_permute]
      .
        rw [h_toNat]
        unfold Tensor.permuteTail
        simp
        apply SEq.of.All_EqGetS.Eq
        .
          intro t
          have h_t := LtVal t
          let ⟨k', k, h_k'k⟩ := Any_EqAddMul.of.Lt_Mul h_t
          have h_k := LtVal k
          have h_k' := LtVal k'
          simp [GetFlatten.eq.Get.of.Eq_AddMul h_k'k.symm]
          rw [GetCast.eq.Get.of.Eq.Lt]
          .
            simp only [ProdAppend.eq.MulProdS] at h_k'
            let ⟨i', j', h_i'j'⟩ := Any_EqAddMul.of.Lt_Mul h_k'
            have h_j' := LtVal j'
            simp [GetFlatten.eq.Get.of.Eq_AddMul h_i'j'.symm]
            unfold Tensor.rotate
            simp only [GetElem.getElem]
            repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
            .
              sorry
            .
              rw [MulProdS.eq.ProdAppend]
              convert h_j'
              simp [LengthPermute.eq.Length]
              rw [EqMin.of.Lt (by omega), Add.comm (a := 1)]
              simp
              rw [Rotate.eq.AppendDrop__Take.of.Le_Length (n := d)]
              simp [LengthPermute.eq.Length]
              omega
            .
              rw [MulProdS.eq.ProdAppend]
            .
              convert h_j'
              simp [LengthPermute.eq.Length]
              rw [EqMin.of.Lt (by omega), Add.comm (a := 1)]
              simp
              rw [Rotate.eq.AppendDrop__Take.of.Le_Length (n := d)]
              simp [LengthPermute.eq.Length]
              omega
            .
              apply congrArg
              simp [LengthPermute.eq.Length]
              rw [EqMin.of.Lt (by omega), Add.comm (a := 1)]
              simp
              rw [Rotate.eq.AppendDrop__Take.of.Le_Length (n := d)]
              simp [LengthPermute.eq.Length]
              omega
          .
            rwa [MulProdS.eq.ProdAppend]
          .
            rw [MulProdS.eq.ProdAppend]
        .
          rw [MulProdS.eq.ProdAppend]
          apply congrArg
          simp [LengthPermute.eq.Length]
          rw [EqMin.of.Lt (by omega), Add.comm (a := 1)]
          simp
          rw [List.Permute__Neg.eq.Append_AppendRotateTakeDrop] at h_permute
          simp at h_permute
          assumption


-- created on 2025-10-19
