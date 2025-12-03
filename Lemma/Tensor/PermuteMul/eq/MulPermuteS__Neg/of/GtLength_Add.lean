import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EqPermute__0
import Lemma.List.GetPermute__Neg.eq.Get_0.of.Gt
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.Permute__Neg.eq.Cons_EraseIdx
import Lemma.List.Rotate_SubLength_1.eq.Cons_DropLast.of.GtLength_0
import Lemma.Nat.ToNatSub_Neg.eq.Add_1
import Lemma.Tensor.Cast_Mul.eq.MulCastS.of.Eq
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.All_EqGetS.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetPermute__Neg.as.Permute__Neg_Get.of.Lt_Get_0.LtAdd_1Length
import Lemma.Tensor.LengthPermute__Neg.eq.Get_0.of.Gt
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteTailMul.eq.MulPermuteTailS
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
import Lemma.Tensor.SEqPermute__0
import Lemma.Tensor.TensorMul.eq.MulTensorS
import Lemma.Vector.FlattenMul.eq.MulFlattenS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SplitAtMul.eq.MulSplitAtS
open Bool List Nat Tensor Vector
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [Mul α]
-- given
  (h_i : s.length > i + d)
  (A B : Tensor α s) :
-- imply
  (A * B).permute ⟨i + d, h_i⟩ (-d) = A.permute ⟨i + d, h_i⟩ (-d) * B.permute ⟨i + d, h_i⟩ (-d) := by
-- proof
  induction i generalizing s A B d with
  | zero =>
    have h_toNat := ToNatSub_Neg.eq.Add_1 d
    rw [@Tensor.Permute.eq.Ite]
    simp
    have h_min : (d + 1) ⊓ s.length - 1 = d := by omega
    split_ifs with h_d h_d_neg h_d_end
    ·
      subst h_d
      have h_all := SEqPermute__0 (i := ⟨0, h_i⟩) (s := s) (α := α)
      have h_A := h_all A
      have h_B := h_all B
      have h_A_mul_B := SEqMulS.of.SEq.SEq h_A h_B
      apply Eq.of.SEq
      apply SEq.symm ∘ SEq.trans h_A_mul_B
      have h_s := Eq_Permute__0 ⟨0, h_i⟩
      rw [@Tensor.Cast_Mul.eq.MulCastS.of.Eq (h := h_s)]
      apply SEq.of.EqCast.Eq (h := h_s)
      rw [@Tensor.Cast_Mul.eq.MulCastS.of.Eq (h := h_s)]
    ·
      omega
    ·
      simp [@Tensor.Permute.eq.Ite]
      split_ifs
      have h_permute : s.take (s.length - (1 - -(d : ℤ)).toNat) ++ (s.drop (s.length - (1 - -(d : ℤ)).toNat)).rotate ((1 - -(d : ℤ)).toNat ⊓ s.length - 1) = s.permute ⟨0 + d, h_i⟩ (-(d : ℤ)) := by 
        simp only [h_toNat]
        simp [h_min]
        rw [Permute__Neg.eq.Cons_EraseIdx]
        simp [show (s.length - (d + 1)) = 0 by omega]
        simp [h_d_end]
        apply Rotate_SubLength_1.eq.Cons_DropLast.of.GtLength_0
        omega
      rw [MulCastS.eq.Cast_Mul.of.Eq h_permute]
      apply EqCastS.of.SEq.Eq h_permute
      rw [PermuteTailMul.eq.MulPermuteTailS]
    ·
      simp [@Tensor.Permute.eq.Ite]
      split_ifs
      apply Eq.of.EqDataS
      simp [DataMul.eq.MulDataS]
      apply EqCast.of.SEq.Eq
      ·
        simp only [h_toNat]
        simp [Permute__Neg.eq.Append_AppendRotateDropTake, h_min]
      ·
        rw [SplitAtMul.eq.MulSplitAtS]
        rw [TensorMul.eq.MulTensorS]
        rw [PermuteTailMul.eq.MulPermuteTailS]
        rw [DataMul.eq.MulDataS]
        rw [FlattenMul.eq.MulFlattenS]
        apply SEq.of.All_EqGetS.Eq.fin
        ·
          intro t
          have h_t := t.isLt
          simp [@Vector.GetMul.eq.MulGetS.fin]
          repeat rw [GetCast.eq.Get.of.Eq.fin]
          repeat {
            simp only [h_toNat]
            simp [Permute__Neg.eq.Append_AppendRotateDropTake, h_min]
          }
        ·
          simp only [h_toNat]
          simp [Permute__Neg.eq.Append_AppendRotateDropTake, h_min]
  | succ i ih =>
    apply Eq.of.All_EqGetS.GtLength_0 (h := by simp; omega)
    intro t
    have h_t := t.isLt
    rw [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin _ h_t]
    simp [GetPermute__Neg.eq.Get_0.of.Gt (by simp) (d := d) (s := s) (i := ⟨i + 1 + d, h_i⟩)] at h_t
    have h_all := GetPermute__Neg.as.Permute__Neg_Get.of.Lt_Get_0.LtAdd_1Length (s := s) (i := i + d) (k := t) (by grind) h_t (d := d) (α := α) (by grind)
    have h_A := h_all A
    have := SEqPermuteS.of.SEq.Eq.Eq.GtLength (s := s) (i := i + d + 1) (i' := i + 1 + d) (d := -d) (d' := -d) (by omega) (by omega) (by omega) (by rfl) (A := A)
    have := SEqGetS.of.SEq.GtLength.fin (i := t) (by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]) this
    have h_A := this.symm.trans h_A
    have h_B := h_all B
    have := SEqPermuteS.of.SEq.Eq.Eq.GtLength (s := s) (i := i + d + 1) (i' := i + 1 + d) (d := -d) (d' := -d) (by omega) (by omega) (by omega) (by rfl) (A := B)
    have := SEqGetS.of.SEq.GtLength.fin (i := t) (by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]) this
    have h_B := this.symm.trans h_B
    have h_A_mul_B := SEqMulS.of.SEq.SEq h_A h_B
    apply Eq.of.SEq
    apply SEq.symm ∘ SEq.trans h_A_mul_B
    rw [← ih (s := s.tail) (by grind) (A.get ⟨t, by grind⟩) (B.get ⟨t, by grind⟩) (d := d)]
    have h_AB := h_all (A * B)
    simp [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin _ h_t] at h_AB
    have := SEqPermuteS.of.SEq.Eq.Eq.GtLength (s := s) (i := i + d + 1) (i' := i + 1 + d) (d := -d) (d' := -d) (by omega) (by omega) (by omega) (by rfl) (A := A * B)
    have := SEqGetS.of.SEq.GtLength.fin (i := t) (by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]) this
    have h_AB := this.symm.trans h_AB
    exact h_AB.symm


-- created on 2025-12-02
-- updated on 2025-12-03
