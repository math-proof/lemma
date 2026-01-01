import sympy.vector.Basic
import sympy.Basic


@[main, comm, fin, fin.comm]
private lemma main
  [Neg α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (-x)[i] = -x[i] := by
-- proof
  simp [Neg.neg]


-- created on 2025-10-04
