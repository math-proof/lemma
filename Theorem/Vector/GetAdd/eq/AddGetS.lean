module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path, fin]
public theorem Vector.GetAdd.eq.AddGetS
  [Add α]
  (a b : List.Vector α n)
  (i : Fin n) :
  (a + b)[i] = a[i] + b[i] := by
  conv in a + b =>
    simp [HAdd.hAdd]
  simp [Add.add]
  simp [GetElem.getElem]

public theorem Vector.GetAdd.eq.AddGetS.fin
  [Add α]
  (a b : List.Vector α n)
  (i : Fin n) :
  (a + b).get i = a.get i + b.get i := by
  simpa [GetElem.getElem] using Vector.GetAdd.eq.AddGetS a b i
