import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData1'1
import Lemma.Vector.Div.eq.One.of.All_Ne_0
open Tensor Vector


@[main]
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


@[main]
private lemma fin
  [GroupWithZero α]
  {X : Tensor α s}
-- given
  (h : ∀ i : Fin s.prod, X.data.get i ≠ 0) :
-- imply
  X / X = 1 := by
-- proof
  apply main h


-- created on 2025-11-28
