module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic.Part2
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path, fin]
public theorem Vector.GetMul.eq.MulGetS
  [Mul α]
  (a b : List.Vector α n)
  (i : Fin n) :
  (a * b)[i] = a[i] * b[i] := by
  conv in a * b =>
    simp [HMul.hMul]
  simp [Mul.mul]
  simp [GetElem.getElem]

public theorem Vector.GetMul.eq.MulGetS.fin
  [Mul α]
  (a b : List.Vector α n)
  (i : Fin n) :
  (a * b).get i = a.get i * b.get i := by
  simpa [GetElem.getElem] using Vector.GetMul.eq.MulGetS a b i
