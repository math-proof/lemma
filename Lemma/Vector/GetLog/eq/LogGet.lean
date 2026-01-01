import sympy.Basic
import sympy.vector.functions


@[main, fin]
private lemma main
  [Log α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (log x)[i] = log x[i] := by
-- proof
  simp [Log.log]


-- created on 2025-12-04
