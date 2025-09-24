import Lemma.Vector.Eq.of.All_EqGetS
import Lemma.Vector.EqGet0'0
open Vector


@[main]
private lemma main
  [Zero α]
  {a : List.Vector α n}
-- given
  (h : ∀ i, a.get i = 0) :
-- imply
  a = 0 := by
-- proof
  apply Eq.of.All_EqGetS.fin
  simpa [EqGet0'0.fin]


-- created on 2025-09-24
