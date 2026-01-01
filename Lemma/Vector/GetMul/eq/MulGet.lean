import sympy.vector.vector
import sympy.Basic


@[main, fin]
private lemma main
  [Mul α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x * a)[i] = x[i] * a := by
-- proof
  simp [HMul.hMul]


-- created on 2025-09-22
