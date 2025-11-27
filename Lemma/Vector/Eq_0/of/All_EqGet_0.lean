import Lemma.Vector.EqGet0_0
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
  ext i
  simp_all [EqGet0_0.fin]



-- created on 2025-09-24
