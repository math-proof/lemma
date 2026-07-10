import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.tensor.Basic
open Bool List


@[main, cast]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  (X.repeat d n).data ≃ ((X.data.splitAt d).map (·.repeat n)).flatten := by
-- proof
  apply SEq.of.Eq_Cast
  simp [Tensor.repeat]
  simp [ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength d.isLt]


-- created on 2025-11-18
