import Lemma.Vector.EqGet1_1.of.Lt
open Vector


@[main, fin]
private lemma main
  [One α]
  {a : List.Vector α n}
-- given
  (h : a = 1)
  (h_i : i < n) :
-- imply
  a[i] = 1 :=
-- proof
  h.symm.subst (motive := fun a : List.Vector α n => a[i] = 1) (EqGet1_1.of.Lt h_i)


-- created on 2025-09-23
