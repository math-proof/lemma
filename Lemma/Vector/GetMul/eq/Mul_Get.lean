import sympy.Basic
import sympy.vector.vector


@[main, fin]
private lemma main
  [Mul α]
-- given
  (a : α)
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  (a * x)[i] = a * x[i] := by
-- proof
  simp [HMul.hMul]


-- created on 2026-01-06
