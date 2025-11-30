import Lemma.Rat.EqDiv_0'0
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqGet0_0
open Vector Rat


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (x : List.Vector α n) :
-- imply
  x / 0 = 0 := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGet0_0]
  simp [HDiv.hDiv]
  simp [Div.div]
  simp [GetElem.getElem]
  right
  rw [EqGet0_0.fin]


-- created on 2025-11-30
