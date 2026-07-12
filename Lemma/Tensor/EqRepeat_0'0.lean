import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.ProdSet__Mul_Get.eq.Mul_Prod
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.EqRepeat_0'0
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Bool Fin List Tensor Vector


@[main]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (d : Fin s.length) :
-- imply
  X.repeat d 0 = 0 := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.repeat
  simp [EqData0'0]
  apply EqCast.of.SEq.Eq (by erw [ProdSet__Mul_Get.eq.Mul_Prod d 0]; simp)
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_t := t.isLt
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    rw [EqRepeat_0'0]
    simp [EqGet0_0.fin]
  ·
    erw [ProdSet__Mul_Get.eq.Mul_Prod d 0]
    simp


-- created on 2026-07-12
