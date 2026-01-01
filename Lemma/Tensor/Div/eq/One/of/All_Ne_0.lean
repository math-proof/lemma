import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData1'1
import Lemma.Vector.Div.eq.One.of.All_Ne_0
open Tensor Vector


@[main, fin 1]
private lemma main
  [GroupWithZero α]
  {X : Tensor α s}
-- given
  (h : ∀ i : Fin s.prod, X.data[i] ≠ 0) :
-- imply
  X / X = 1 := by
-- proof
  apply Eq.of.EqDataS
  rw [DataDiv.eq.DivDataS]
  rw [EqData1'1]
  apply Div.eq.One.of.All_Ne_0 h


-- created on 2025-11-28
