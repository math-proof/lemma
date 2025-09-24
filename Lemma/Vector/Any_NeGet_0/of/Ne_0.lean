import stdlib.List.Vector.Basic
import Lemma.Vector.Eq_0.of.All_EqGet_0
open Vector


@[main]
private lemma main
  [Zero α]
  {a : List.Vector α n}
-- given
  (h : a ≠ 0) :
-- imply
  ∃ i, a.get i ≠ 0 := by
-- proof
  contrapose! h
  apply Eq_0.of.All_EqGet_0 h


-- created on 2025-09-23
-- updated on 2025-09-24
