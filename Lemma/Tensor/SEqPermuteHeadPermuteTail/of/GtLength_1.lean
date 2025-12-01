import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.EqRotateRotate.of.Add.eq.Length
import Lemma.List.EqTake.of.LeLength
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailRotate.eq.Take.of.GtLength_0
import Lemma.List.TakeRotate.eq.Drop.of.EqLength_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMul_1.of.Eq_1
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Gt_0.of.Gt
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat List Bool Tensor Vector Fin


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
    simp_all [Drop.eq.Nil.of.LeLength, EqTake.of.LeLength]
    apply EqRotateRotate.of.Add.eq.Length
    omega
  ·
    simp
    apply SEqCast.of.SEq.Eq
    ·
      rw [MulProdS.eq.ProdAppend]
    ·
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := t.isLt
        have h_drop := Drop.eq.Nil.of.LeLength (show (s.rotate (s.length - 1)).length ≤ s.length by simp)
        simp
        rw [GetFlatten.eq.Get.of.Eq_AddMul (i := ⟨t, by simp [h_drop] at h_t; simpa⟩) (j := ⟨0, by simp [h_drop]⟩) (by simp [h_drop])]
        unfold Tensor.rotate
        simp [GetElem.getElem]
        repeat rw [GetCast.eq.Get.of.Eq.fin]
        ·
          simp
          have : ((s.take (s.length - s.length) ++ (s.drop (s.length - s.length)).rotate (s.length ⊓ s.length - 1)).drop s.length).prod = 1 := by
            simp [h_drop]
          simp only [EqMul_1.of.Eq_1 this] at h_t
          simp only [Rotate.eq.AppendDrop__Take (n := 1), ProdAppend.eq.MulProdS] at h_t
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
          have h_q := q.isLt
          have h_r := r.isLt
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
          rw [GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp_all [Drop.eq.Nil.of.LeLength, EqTake.of.LeLength]
          simp [EqMod.of.Lt h] at h_q h_r
          rw [TailRotate.eq.Take.of.GtLength_0 (by omega)] at h_q
          rw [TakeRotate.eq.Drop.of.EqLength_Add (by omega)] at h_r
          let s' := s.drop (s.length - s.length)
          have h_lt : r * (s.take (s.length - 1)).prod + q < (s'.drop ((s.length ⊓ s.length - 1) % s'.length)).prod * (s'.take ((s.length ⊓ s.length - 1) % s'.length)).prod := by
            simp [s']
            apply AddMul.lt.Mul.of.Lt.Lt h_r h_q
          simp [EqMod.of.Lt h]
          simp [TailRotate.eq.Take.of.GtLength_0 (by omega)]
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            have := h_lt
            simp [s'] at this
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by simp⟩) (j := ⟨r * (s.take (s.length - 1)).prod + q, by simpa [Rotate.eq.AppendDrop__Take]⟩) (by simp)]
            simp
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
              let ⟨h_q'_div, h_r'_div⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              simp [s'] at h_q'_div h_r'_div
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              rw [GetTranspose.eq.Get.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              apply congrArg
              simp [TakeRotate.eq.Drop.of.EqLength_Add (show s.length = s.length - 1 + 1 by omega)]
              simp [h_q'_div, h_r'_div]
              simp [EqMod.of.Lt h_q]
              rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
              simp
              right
              exact h_q
            ·
              simp [Rotate.eq.AppendDrop__Take]
          ·
            rw [MulProdS.eq.ProdAppend]
        ·
          simp [Rotate.eq.AppendDrop__Take]
      ·
        simp [ProdRotate.eq.Prod]


-- created on 2025-10-26
