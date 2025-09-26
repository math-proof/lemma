import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqDiv0'0
open Tensor Vector


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (X : Tensor α s):
-- imply
  0 / X = 0 := by
-- proof
  apply Eq.of.EqDataS
  rw [EqData0'0]
  simp [HDiv.hDiv]
  simp [Div.div]
  rw [EqData0'0]
  apply EqDiv0'0


-- created on 2025-09-04
-- updated on 2025-09-26
