import sympy.vector.functions
import sympy.Basic


@[main]
private lemma main
  [Exp α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (exp x)[i] = exp x[i] := by
-- proof
  simp [Exp.exp]


@[main]
private lemma fin
  [Exp α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (exp x).get i = exp (x.get i) :=
-- proof
  main x i


-- created on 2025-10-08
