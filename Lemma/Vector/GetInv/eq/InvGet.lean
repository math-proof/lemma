import sympy.vector.Basic
import sympy.Basic


@[main, comm]
private lemma main
  [Inv α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  x⁻¹[i] = x[i]⁻¹ := by
-- proof
  simp [Inv.inv]


@[main, comm]
private lemma fin
  [Inv α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  x⁻¹.get i = (x.get i)⁻¹ :=
-- proof
  main x i


-- created on 2025-09-23
