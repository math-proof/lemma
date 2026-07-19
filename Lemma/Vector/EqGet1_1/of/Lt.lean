import Lemma.Vector.EqGet1_1
open Vector


@[main, subst 1]
private lemma main
  [One α]
-- given
  (h_i : i < n) :
-- imply
  (1 : List.Vector α n)[i] = 1 :=
-- proof
  EqGet1_1 ⟨i, h_i⟩


-- created on 2025-09-23
-- updated on 2026-07-19
