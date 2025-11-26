import Lemma.Tensor.DataRepeat.eq.Cast_FlattenMapSplitAtData
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Bool.SEq.is.EqCast.of.Eq
open Tensor Bool List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  (X.repeat n d).data ≃ ((X.data.splitAt d).map (·.repeat n)).flatten := by
-- proof
  apply SEq.of.Eq_Cast
  apply DataRepeat.eq.Cast_FlattenMapSplitAtData
  simp [ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength d.isLt]


-- created on 2025-11-18
