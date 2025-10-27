import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqDiv0'0
import Lemma.Rat.EqDiv0'0
open Tensor Vector Rat


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
  apply EqDiv0'0 X.data


@[main]
private lemma scalar
  [GroupWithZero α]
-- given
  (x : α)
  (s : List ℕ) :
-- imply
  (0 : Tensor α s) / x = 0 := by
-- proof
  apply Eq.of.EqDataS
  rw [EqData0'0]
  simp [HDiv.hDiv]
  rw [EqData0'0]
  ext i
  simp
  rw [EqGet0'0.fin]
  apply EqDiv0'0 (a := x)


-- created on 2025-09-04
-- updated on 2025-09-26
