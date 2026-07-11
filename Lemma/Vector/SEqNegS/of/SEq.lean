import Lemma.Bool.SEqUFnS.of.SEq
import sympy.vector.Basic
open Bool


@[main]
private lemma main
  [Neg α]
  {x : List.Vector α n}
  {y : List.Vector α n'}
-- given
  (h : x ≃ y) :
-- imply
  -x ≃ -y := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2025-12-04
