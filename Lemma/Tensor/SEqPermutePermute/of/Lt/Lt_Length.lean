import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.List.TakePermute.eq.Take
import Lemma.Nat.EqSub_Sub.of.Gt
import Lemma.Nat.EqMinSub
import Lemma.List.RotateDropPermute.eq.Drop
import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Int.EqToNat
import Lemma.Nat.SubSub
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.DropPermute.eq.Drop.of.Add.lt.Length
import Lemma.Nat.Add
import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.TakeDrop.eq.RotateDropTakePermute.of.Add.lt.Length
import Lemma.Tensor.PermuteTailCast.eq.Cast_PermuteTail.of.Eq
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.List.Rotate.eq.Permute.of.GtLength_0
import Lemma.List.EqRotateRotate.of.Le_Length
import Lemma.Tensor.PermuteTail.as.Rotate.of.Eq_Length
open List Tensor Bool Nat Int


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_j : j < s.length)
  (h : i < j)
  (X : Tensor α s) :
-- imply
  let d := j - i
  (X.permute ⟨i, by linarith⟩ d).permute ⟨j, by simpa [LengthPermute.eq.Length]⟩ (-d) ≃ X := by
-- proof
  intro d
  rw [Permute.eq.Ite (d := ⟨j, by simpa [LengthPermute.eq.Length]⟩) (k := -d)]
  have h_toNat : (1 - -(d : ℤ)).toNat = 1 + d := by
    rw [Sub_Neg.eq.Add]
    have := AddCoeS.eq.CoeAdd (α := ℤ) 1 d
    rw [Cast.eq.OfNat] at this
    rw [this]
    rw [EqToNat]
  split_ifs with h_sub h_pos h_j_0 h_j_length
  repeat omega
  simp [LengthPermute.eq.Length] at h_j_length
  subst h_j_length
  simp
  apply SEqCast.of.SEq.Eq.Eq
  ·
    rw [EqPermutePermute.of.In_Ioo_Length ⟨h, h_j⟩]
    simp [LengthPermute.eq.Length]
    rw [(show (1 + d : ℤ).toNat = s.length - i by omega)]
    rw [EqSub_Sub.of.Gt (by linarith)]
    rw [EqMinSub]
    rw [(show (d : ℤ) = (s.length - i - 1 : ℕ) by omega)]
    rw [TakePermute.eq.Take ⟨i, by linarith⟩ (s.length - i - 1)]
    simp [RotateDropPermute.eq.Drop (i := ⟨i, by linarith⟩)]
  ·
    rw [EqPermutePermute.of.In_Ioo_Length ⟨by omega, by omega⟩]
  ·
    simp at h_sub
    simp at h_j_length
    rw [h_toNat]
    rw [Permute.eq.Ite (d := ⟨i, by linarith⟩) (k := ↑d)]
    simp
    split_ifs with h_pos? h_i_0 h_i_length
    ·
      subst d h_i_0
      simp
      rw [EqAdd_Sub.of.Ge (by linarith)]
      rw [PermuteTailCast.eq.Cast_PermuteTail.of.Eq]
      ·
        apply SEqCast.of.SEq.Eq.Eq
        ·
          rw [EqAddSub.of.Ge (by linarith)]
          simp [Permute.eq.Rotate.of.GtLength_0]
        ·
          simp [Permute.eq.Rotate.of.GtLength_0]
          rw [EqRotateRotate.of.Le_Length]
          linarith
        ·
          rw [EqAddSub.of.Ge (by linarith)]
          have := PermuteTail.as.Rotate.of.Eq_Length (n := s.length) (by simp) (X.permuteHead s.length)
          apply SEq.trans this
          sorry
      ·
        rw [EqAddSub.of.Ge (by linarith)]
        simp
        apply Rotate.eq.Permute.of.GtLength_0
    ·
      sorry
    ·
      omega
    ·
      omega
  ·
    simp
    apply SEq.of.SEqDataS.Eq
    ·
      rw [EqPermutePermute.of.In_Ioo_Length ⟨by omega, by omega⟩]
    ·
      simp
      apply SEqCast.of.SEq.Eq
      ·
        simp at h_sub
        simp at h_j_length
        rw [h_toNat]
        rw [EqPermutePermute.of.In_Ioo_Length ⟨by omega, by omega⟩]
        simp [LengthPermute.eq.Length]
        repeat rw [EqMin.of.Le (by omega)]
        rw [EqSubAdd.left]
        rw [@Nat.Sub_Add.eq.SubSub]
        rw [EqSubAdd]
        have h_j : j = d + i := by omega
        simp [h_j]
        rw [TakeTake.eq.Take.of.Ge (by omega)]
        rw [TakePermute.eq.Take ⟨i, by linarith⟩]
        conv_lhs =>
          arg 2
          rw [Add.comm (a := d) (b := i)]
        rw [DropPermute.eq.Drop.of.Add.lt.Length (i := ⟨i, by linarith⟩)] <;>
          simp
        ·
          have h_drop := ProdDrop.eq.MulProdS s i (d + 1)
          rw [Add_Add.eq.AddAdd] at h_drop
          have h_rotate := TakeDrop.eq.RotateDropTakePermute.of.Add.lt.Length (s := s) (i := ⟨i, by linarith⟩) (d := d) (by grind)
          simp at h_rotate
          rw [← h_rotate]
          rw [MulMul.eq.Mul_Mul]
          simp [← h_drop]
        ·
          omega
      ·
        rw [h_toNat]
        sorry


-- created on 2025-10-12
-- updated on 2025-10-18
