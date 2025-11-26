import sympy.tensor.Basic
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  (X.repeat n d).data = cast (by simp [ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength d.isLt]) ((X.data.splitAt d).map (·.repeat n)).flatten := by
-- proof
  simp [Tensor.repeat]


-- created on 2025-11-18
