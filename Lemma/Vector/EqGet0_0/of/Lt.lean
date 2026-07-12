import Lemma.Vector.EqGet0_0
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (h_i : i < n) :
-- imply
  (0 : List.Vector α n)[i] = 0 :=
-- proof
  EqGet0_0 ⟨i, by grind⟩


-- created on 2025-09-04
