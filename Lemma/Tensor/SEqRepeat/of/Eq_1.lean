import Lemma.Tensor.SEqRepeat
open Tensor


@[main, cast]
private lemma main
-- given
  (h : n = 1)
  (X : Tensor α s)
  (d : Fin s.length) :
-- imply
  X.repeat d n ≃ X :=
-- proof
  h.symm.subst (motive := fun n => X.repeat d n ≃ X) (SEqRepeat X d)


-- created on 2026-07-12
