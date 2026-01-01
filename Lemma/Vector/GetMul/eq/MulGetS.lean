import sympy.vector.Basic
import sympy.Basic


@[main, fin]
private lemma main
  [Mul α]
-- given
  (a b : List.Vector α n)
  (i : Fin n):
-- imply
  (a * b)[i] = a[i] * b[i] := by
-- proof
  conv in a * b =>
    simp [HMul.hMul]
  simp [Mul.mul]
  simp [GetElem.getElem]


-- created on 2025-07-14
