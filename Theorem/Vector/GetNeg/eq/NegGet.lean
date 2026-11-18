module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic.Part2
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path, comm, fin, fin.comm]
public theorem Vector.GetNeg.eq.NegGet
  [Neg α]
  (x : List.Vector α n)
  (i : Fin n) :
  (-x)[i] = -x[i] := by
  simp [Neg.neg]

public theorem Vector.GetNeg.eq.NegGet.fin
  [Neg α]
  (x : List.Vector α n)
  (i : Fin n) :
  (-x).get i = -x.get i := by
  simpa [GetElem.getElem] using Vector.GetNeg.eq.NegGet x i
