module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path, fin, subst 1]
private theorem main
  [One α]
-- given
  (i : Fin n) :
-- imply
  (1 : List.Vector α n)[i] = 1 := by
-- proof
  simp [GetElem.getElem]
  erw [List.Vector.get_replicate]


-- created on 2025-09-23
