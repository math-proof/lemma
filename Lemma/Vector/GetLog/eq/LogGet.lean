import sympy.Basic
import sympy.vector.functions


@[main]
private lemma main
  [Log α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (log x)[i] = log x[i] := by
-- proof
  simp [Log.log]


@[main]
private lemma fin
  [Log α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (log x).get i = log (x.get i) :=
-- proof
  main x i


-- created on 2025-12-04
