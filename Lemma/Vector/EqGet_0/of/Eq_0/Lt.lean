import Lemma.Vector.EqGet_0.of.Eq_0
open Vector


@[main]
private lemma main
  [Zero α]
  {a : List.Vector α n}
-- given
  (h_i : i < n)
  (h : a = 0) :
-- imply
  a[i] = 0 := by
-- proof
  simp [GetElem.getElem]
  apply EqGet_0.of.Eq_0 h


-- created on 2025-09-04
-- updated on 2025-09-23
