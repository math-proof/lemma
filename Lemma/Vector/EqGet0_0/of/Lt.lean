import Lemma.Vector.EqGet0_0
open Vector


@[main, subst 0]
private lemma main
  [Zero α]
-- given
  (h_i : i < n) :
-- imply
  (0 : List.Vector α n)[i] = 0 :=
-- proof
  EqGet0_0 ⟨i, h_i⟩


-- created on 2025-09-04
-- updated on 2026-07-19
