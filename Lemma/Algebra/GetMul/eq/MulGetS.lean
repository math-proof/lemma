import stdlib.List.Vector.Basic
import sympy.Basic


@[main]
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


@[main]
private lemma fin
  [Mul α]
-- given
  (a b : List.Vector α n)
  (i : Fin n):
-- imply
  (a * b).get i = a.get i * b.get i := by
-- proof
  apply main

-- created on 2025-07-14
