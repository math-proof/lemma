module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path, val, fin, subst 0]
public theorem Vector.EqGet0_0
  [Zero α]
  (i : Fin n) :
  (0 : List.Vector α n)[i] = 0 := by
  simp [GetElem.getElem]
  erw [List.Vector.get_replicate]

public theorem Vector.EqGet0_0.fin
  [Zero α]
  (i : Fin n) :
  (0 : List.Vector α n).get i = 0 := by
  simpa [GetElem.getElem] using Vector.EqGet0_0 (n := n) i
