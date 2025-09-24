import Lemma.Vector.Eq.of.All_EqGetS
import Lemma.Vector.EqGet0'0
open Vector


@[main]
private lemma main
  [GroupWithZero α]
-- given
  (n : ℕ) :
-- imply
  (0 : List.Vector α n) / (0 : List.Vector α n) = (0 : List.Vector α n) := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGet0'0]
  simp [HDiv.hDiv]
  simp [Div.div]
  simp [GetElem.getElem]
  rw [EqGet0'0.fin]


-- created on 2025-09-04
