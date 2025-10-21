import Lemma.Tensor.LengthData.eq.Mul_Prod.of.GtLength_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Ne_0
import Lemma.Nat.EqMin.of.Le
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.Le_SubMulS.of.Lt
import Lemma.Nat.LtVal
open Tensor List Nat


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  X.data.length / s[0] ⊓ (s.prod - i * (X.data.length / s[0])) = s.tail.prod := by
-- proof
  rw [LengthData.eq.Mul_Prod.of.GtLength_0 h]
  rw [EqDivMul.of.Ne_0.left]
  ·
    apply EqMin.of.Le
    rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h]
    apply Le_SubMulS.of.Lt
    apply LtVal i
  ·
    apply Ne_0 i


-- created on 2025-06-29
