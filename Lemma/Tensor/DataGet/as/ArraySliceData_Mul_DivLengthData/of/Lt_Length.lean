import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthData.eq.Mul_Prod.of.GtLength_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Ne_0
import Lemma.Tensor.DataGet.as.ArraySliceData_Mul_ProdTail.of.GtLength_0
open Tensor Nat


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have := Lt_Length.of.GtLength_0 h X i
  X[i].data ≃ X.data.array_slice (i * (X.data.length / s[0])) (X.data.length / s[0]) := by
-- proof
  have h_length := LengthData.eq.Mul_Prod.of.GtLength_0 h X
  rw [h_length]
  rw [EqDivMul.of.Ne_0.left]
  ·
    apply DataGet.as.ArraySliceData_Mul_ProdTail.of.GtLength_0 h
  ·
    apply Ne_0 i


-- created on 2025-06-29
