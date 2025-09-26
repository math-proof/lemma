import Lemma.Vector.Eq.of.All_EqGetS
import Lemma.Vector.EqGet0'0
open Vector


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (x : List.Vector α n) :
-- imply
  0 / x = 0 := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGet0'0]
  simp [HDiv.hDiv]
  simp [Div.div]
  simp [GetElem.getElem]
  left
  rw [EqGet0'0.fin]


-- created on 2025-09-04
