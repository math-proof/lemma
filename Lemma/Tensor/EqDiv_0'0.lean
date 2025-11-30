import Lemma.Rat.EqDiv_0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqGet0_0
import Lemma.Vector.EqDiv_0'0
open Tensor Vector Rat


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (X : Tensor α s) :
-- imply
  X / 0 = 0 := by
-- proof
  apply Eq.of.EqDataS
  rw [EqData0'0]
  simp [HDiv.hDiv]
  simp [Div.div]
  rw [EqData0'0]
  apply EqDiv_0'0 X.data


-- created on 2025-11-30
