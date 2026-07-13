import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.tensor.tensor
open List Bool


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  (X.resize d n).data ≃ ((X.data.splitAt d).map (·.resize (n * (s.drop d.succ).prod))).flatten := by
-- proof
  apply SEq.of.Eq_Cast
  simp [Tensor.resize]
  simp [List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength d.isLt]


-- created on 2026-07-13
