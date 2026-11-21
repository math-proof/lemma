module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path, fin, subst 1]
public theorem Vector.EqGet1_1
  [One α]
  (i : Fin n) :
  (1 : List.Vector α n)[i] = 1 := by
  simp [GetElem.getElem]
  erw [List.Vector.get_replicate]

public theorem Vector.EqGet1_1.fin
  [One α]
  (i : Fin n) :
  (1 : List.Vector α n).get i = 1 := by
  simpa [GetElem.getElem] using Vector.EqGet1_1 (n := n) i
