import Lemma.Vector.EqGet1_1
open Vector


@[main]
private lemma main
  [One α]
  {a : List.Vector α n}
-- given
  (h : a = 1)
  (i : Fin n) :
-- imply
  a.get i = 1 :=
-- proof
  h.symm.subst (motive := fun a : List.Vector α n => a.get i = 1) (EqGet1_1 i)


-- created on 2025-09-23
