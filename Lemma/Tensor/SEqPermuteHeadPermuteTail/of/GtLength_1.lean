import Lemma.Nat.EqMul_1.of.Eq_1
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.DropRotate.eq.Take.of.Le_Length
import Lemma.List.EqRotateRotate.of.Le_Length
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.EqRotateRotate.of.Add.eq.Length
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.List.TakeRotate.eq.Drop.of.Le_Length
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.LtVal
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Vector Tensor List Bool Nat


@[main]
private lemma main
-- given
  (h : s.length > 1)
  (X : Tensor α s) :
-- imply
  (X.permuteTail s.length).permuteHead s.length ≃ X := by
-- proof
  have h_0 := Gt_0.of.Gt h
  unfold Tensor.permuteTail Tensor.permuteHead
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    simp
    rw [EqTake.of.Ge_Length (by simp)]
    rw [Drop.eq.Nil.of.Ge_Length (by simp)]
    simp
    apply EqRotateRotate.of.Add.eq.Length
    omega
  ·
    simp
    apply SEqCast.of.SEq.Eq.Eq
    ·
      rw [MulProdS.eq.ProdAppend]
    ·
      apply congrArg
      simp
      rw [EqTake.of.Ge_Length (by simp)]
      rw [Drop.eq.Nil.of.Ge_Length (by simp)]
      simp
      rw [EqRotateRotate.of.Add.eq.Length]
      omega
    ·
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := LtVal t
        have := Drop.eq.Nil.of.Ge_Length (show (s.rotate (s.length - 1)).length ≤ s.length by simp)
        simp [this] at h_t
        simp
        rw [GetFlatten.eq.Get.of.Eq_AddMul (i := ⟨t, by simpa⟩) (j := ⟨0, by simp [this]⟩) (by simp [this])]
        unfold Tensor.rotate
        repeat rw [GetCast.eq.Get.of.Eq.Lt]
        ·
          simp
          have h_t := LtVal t
          have : ((s.take (s.length - s.length) ++ (s.drop (s.length - s.length)).rotate (s.length ⊓ s.length - 1)).drop s.length).prod = 1 := by
            simp [this]
          simp only [Nat.EqMul_1.of.Eq_1 this] at h_t
          simp only [Rotate.eq.AppendDrop__Take (n := 1), ProdAppend.eq.MulProdS] at h_t
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          simp only [GetElem.getElem]
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
          rw [GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [GetCast.eq.Get.of.Eq.Lt.fin]
          .
            sorry
          .
            sorry
          .
            sorry
        ·
          convert h_t
          simp
          sorry
        ·
          rw [MulProdS.eq.ProdAppend]
        ·
          convert h_t
          simp
          sorry
        ·
          apply congrArg
          simp
          sorry
      ·
        simp
        sorry


-- created on 2025-10-26
