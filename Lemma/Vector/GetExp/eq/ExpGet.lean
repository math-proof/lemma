import sympy.vector.functions
import sympy.Basic


@[main, fin]
private lemma main
  [Exp α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (exp x)[i] = exp x[i] := by
-- proof
  simp [Exp.exp]


-- created on 2025-10-08
