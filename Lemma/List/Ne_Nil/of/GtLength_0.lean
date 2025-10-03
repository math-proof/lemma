import Lemma.Algebra.Ne.of.Gt
import Lemma.List.Ne_Nil.of.NeLength_0
open Algebra List


@[main]
private lemma main
  {v : List α}
-- given
  (h : v.length > 0) :
-- imply
  v ≠ [] := by
-- proof
  have h := Ne.of.Gt h
  apply Ne_Nil.of.NeLength_0 h


-- created on 2025-05-08
