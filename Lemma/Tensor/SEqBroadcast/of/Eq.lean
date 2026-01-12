import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.One.of.Ne_0
import Lemma.Nat.EqMulDiv
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Bool Fin Nat Tensor Vector


@[main, comm 1]
private lemma main
  [Mul α] [Zero α] [Add α]
  {A : Tensor α s}
-- given
  (h : s' = s) :
-- imply
  A.broadcast s' (by simp_all) ≃ A := by
-- proof
  unfold Tensor.broadcast
  apply SEq.of.SEqDataS.Eq h
  simp
  apply SEqCast.of.SEq.Eq
  ·
    simp [h]
    apply EqMulDiv
  ·
    unfold List.Vector.repeat
    rw [h]
    apply SEq.of.All_EqGetS.Eq.fin
    ·
      intro t
      have h_t := t.isLt
      let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
      simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
      simp [h_qr]
      have h_q := q.isLt
      simp [Div.eq.One.of.Ne_0 (show s.prod ≠ 0 by grind)] at h_q
      simp [h_q]
    ·
      apply EqMulDiv


-- created on 2026-01-12
