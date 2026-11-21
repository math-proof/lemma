module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path, comm, fin, fin.comm]
public theorem Vector.GetInv.eq.InvGet
  [Inv α]
  (x : List.Vector α n)
  (i : Fin n) :
  x⁻¹[i] = x[i]⁻¹ := by
  simp [Inv.inv]

public theorem Vector.GetInv.eq.InvGet.fin
  [Inv α]
  (x : List.Vector α n)
  (i : Fin n) :
  x⁻¹.get i = (x.get i)⁻¹ := by
  simpa [GetElem.getElem] using Vector.GetInv.eq.InvGet x i
