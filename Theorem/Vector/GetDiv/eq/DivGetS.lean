module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic.Part2
public import Instance.Data.Vector.Basic.Arithmetic
public import Theorem.Vector.Div.eq.Map₂

public section

open Vector


@[path, fin]
public theorem Vector.GetDiv.eq.DivGetS
  [Div α]
  (a b : List.Vector α n)
  (i : Fin n) :
  (a / b)[i] = a[i] / b[i] := by
  simp [GetElem.getElem]
  rw [Div.eq.Map₂]
  rw [List.Vector.get_map₂]

public theorem Vector.GetDiv.eq.DivGetS.fin
  [Div α]
  (a b : List.Vector α n)
  (i : Fin n) :
  (a / b).get i = a.get i / b.get i := by
  simpa [GetElem.getElem] using Vector.GetDiv.eq.DivGetS a b i
