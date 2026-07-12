import Lemma.Vector.SEqRepeat_1
open Vector


@[main, cast]
private lemma main
-- given
  (h : d = 1)
  (x : List.Vector α n) :
-- imply
  x.repeat d ≃ x :=
-- proof
  h.symm.subst (motive := fun d => x.repeat d ≃ x) (SEqRepeat_1 x)


-- created on 2026-01-10
