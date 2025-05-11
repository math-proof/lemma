import stdlib.List.Vector
import Lemma.Algebra.Eq.of.EqValS
open Algebra


@[main]
private lemma main
  {a b : List.Vector α n}
-- given
  (h : a.toList = b.toList) :
-- imply
  a = b := by
-- proof
  simp [List.Vector.toList]at h
  apply Eq.of.EqValS h


-- created on 2025-05-11
