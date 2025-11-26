import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.List.EqRotateRotate.of.GeLength
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.List.ProdRotate.eq.Prod
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.List.EqAppendTake__Drop
import Lemma.Nat.Sub_Mod.eq.ModSub
import Lemma.List.TakeRotate.eq.Drop
import Lemma.Nat.EqMod.of.Lt
import Lemma.List.DropRotate.eq.Take
import Lemma.Tensor.SEqRotate_Length
import Lemma.List.LengthRotate.eq.Length
import Lemma.Tensor.SEqRotate_0
import Lemma.Nat.Sub.eq.Zero
open Vector Tensor List Bool Nat


@[main]
private lemma main
-- given
  (h : i ≤ s.length)
  (X : Tensor α s) :
-- imply
  (X.rotate i).rotate (s.length - i) ≃ X := by
-- proof
  if h_i : i = s.length ∨ i = 0 then
    obtain h_i | h_i := h_i <;>
      subst h_i
    ·
      have := SEqRotate_0 (X.rotate s.length)
      rw [← Sub.eq.Zero s.length] at this
      apply SEq.trans this
      apply SEqRotate_Length
    ·
      have := SEqRotate_Length (X.rotate 0)
      rw [← LengthRotate.eq.Length s 0]
      apply SEq.trans this
      apply SEqRotate_0
  else
    unfold Tensor.rotate
    apply SEq.of.SEqDataS.Eq
    ·
      rw [EqRotateRotate.of.GeLength h]
    ·
      simp
      apply SEqCast.of.SEq.Eq.Eq
      ·
        rw [MulProdS.eq.ProdAppend]
        rw [AppendDrop__Take.eq.Rotate]
      ·
        rw [EqRotateRotate.of.GeLength h]
      ·
        apply SEq.of.All_EqGetS.Eq
        ·
          intro t
          have h_t := t.isLt
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
          rw [GetTranspose.eq.Get]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
          simp at h_qr ⊢
          simp [GetElem.getElem]
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp at h_i
            have : NeZero i := ⟨by omega⟩
            have h_i : i < s.length := by omega
            have := Sub_Mod.eq.ModSub (m := s.length) (n := i) h_i
            let n := (List.take (i % s.length) s).prod
            let m := (List.drop (i % s.length) s).prod
            have h_r := r.isLt
            simp at h_r
            have h_take := TakeRotate.eq.Drop s i
            have h_mod := EqMod.of.Lt h_i
            rw [h_mod] at h_take
            rw [h_take] at h_r
            have h_q := q.isLt
            simp at h_q
            have h_drop := DropRotate.eq.Take s i
            rw [h_mod] at h_drop
            rw [h_drop] at h_q
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨r, by simp [h_mod, h_r]⟩) (j := ⟨q, by simpa [h_mod]⟩)]
            ·
              rw [GetTranspose.eq.Get.fin]
              rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              simp at ⊢ h_qr
              rw [h_take] at h_qr
              simp [h_qr]
              simp [h_mod]
            ·
              simp
              left
              rw [h_drop]
              rw [h_mod]
          ·
            rw [MulProdS.eq.ProdAppend]
            rw [AppendDrop__Take.eq.Rotate]
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [AppendDrop__Take.eq.Rotate]
          rw [EqRotateRotate.of.GeLength h]


-- created on 2025-10-18
-- updated on 2025-10-19
