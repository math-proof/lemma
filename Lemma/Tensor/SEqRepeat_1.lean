import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqMod.of.Lt
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin Tensor Vector Nat


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (d : Fin s.length) :
-- imply
  X.repeat 1 d ≃ X := by
-- proof
  unfold Tensor.repeat
  apply SEq.of.SEqDataS.Eq
  ·
    simp
  ·
    simp
    apply SEqCast.of.SEq.Eq
    ·
      simp
    ·
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        simp [GetRepeat.eq.Get_Mod.fin]
        simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        have h_r := r.isLt
        conv_rhs at h_r => simp
        simp [EqMod.of.Lt h_r]
        simp [h_qr]
      ·
        simp


-- created on 2026-01-13
