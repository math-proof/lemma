import Lemma.Vector.EqGet0_0.of.Lt
open Vector


@[main, fin]
private lemma main
  [Zero α]
  {a : List.Vector α n}
-- given
  (h : a = 0)
  (h_i : i < n) :
-- imply
  a[i] = 0 :=
-- proof
  h.symm.subst (motive := fun a : List.Vector α n => a[i] = 0) (EqGet0_0.of.Lt h_i)


-- created on 2025-09-04
-- updated on 2025-09-23
