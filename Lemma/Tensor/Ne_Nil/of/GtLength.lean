import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.Tensor.GtLength_0.of.GtLength
import sympy.tensor.Basic
open Tensor List


@[main]
private lemma main
  {X : Tensor α s}
-- given
  (h : X.length > i) :
-- imply
  s ≠ [] := by
-- proof
  have h := GtLength_0.of.GtLength h
  apply Ne_Nil.of.GtLength_0 h


-- created on 2025-06-29
