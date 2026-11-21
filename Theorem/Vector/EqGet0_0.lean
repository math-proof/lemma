module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path, val, fin, subst 0]
private theorem main
  [Zero α]
-- given
  (i : Fin n) :
-- imply
  (0 : List.Vector α n)[i] = 0 := by
-- proof
  simp [GetElem.getElem]
  erw [List.Vector.get_replicate]


-- created on 2025-09-04
