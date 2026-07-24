import sympy.vector.vector
import Lemma.Vector.Eq.of.Val
open Vector


@[main]
private lemma main
  {a b : List.Vector α n}
-- given
  (h : a.toList = b.toList) :
-- imply
  a = b := by
-- proof
  simp [List.Vector.toList]at h
  apply Eq.of.Val h


-- created on 2025-05-11
