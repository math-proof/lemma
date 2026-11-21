module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path, comm, fin, fin.comm]
private theorem main
  [Inv α]
-- given
  (x : List.Vector α n)
  (i : Fin n) :
-- imply
  x⁻¹[i] = x[i]⁻¹ := by
-- proof
  simp [Inv.inv]


-- created on 2025-09-23
