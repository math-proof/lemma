import sympy.vector.Basic
import sympy.Basic


@[main, comm, fin, fin.comm]
private lemma main
  [Inv α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  x⁻¹[i] = x[i]⁻¹ := by
-- proof
  simp [Inv.inv]


-- created on 2025-09-23
