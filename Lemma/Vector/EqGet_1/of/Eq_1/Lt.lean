import Lemma.Vector.EqGet_1.of.Eq_1
open Vector


@[main]
private lemma main
  [One α]
  {a : List.Vector α n}
-- given
  (h_i : i < n)
  (h : a = 1) :
-- imply
  a[i] = 1 := by
-- proof
  simp [GetElem.getElem]
  apply EqGet_1.of.Eq_1 h


-- created on 2025-09-23
