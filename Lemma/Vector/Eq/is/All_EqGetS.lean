import sympy.Basic
import sympy.vector.vector


@[main, comm, mp, mpr, fin, fin.comm, fin.mp, fin.mpr]
private lemma main
-- given
  (a b : List.Vector α n) :
-- imply
  a = b ↔ ∀ i : Fin n, a[i] = b[i] := by
-- proof
  aesop


-- created on 2025-07-11
