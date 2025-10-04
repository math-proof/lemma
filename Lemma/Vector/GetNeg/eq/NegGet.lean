import sympy.vector.Basic
import sympy.Basic


@[main, comm]
private lemma main
  [Neg α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (-x)[i] = -x[i] := by
-- proof
  simp [Neg.neg]


@[main, comm]
private lemma fin
  [Neg α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (-x).get i = -x.get i := by
-- proof
  apply main


-- created on 2025-10-04
