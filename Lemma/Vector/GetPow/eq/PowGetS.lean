import sympy.vector.Basic
import sympy.Basic


@[main, fin]
private lemma main
  [HPow α β α]
-- given
  (a : List.Vector α n)
  (b : List.Vector β n)
  (i : Fin n) :
-- imply
  (a ^ b)[i] = a[i] ^ b[i] := by
-- proof
  simp [HPow.hPow, GetElem.getElem]


-- created on 2026-08-23
