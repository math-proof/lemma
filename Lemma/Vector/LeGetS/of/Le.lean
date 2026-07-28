import sympy.Basic
import sympy.vector.Basic


@[main, fin]
private lemma main
  [LE α]
  {a b : List.Vector α n}
-- given
  (h : a ≤ b)
  (i : Fin n) :
-- imply
  a[i] ≤ b[i] :=
-- proof
  h i


-- created on 2026-07-27
