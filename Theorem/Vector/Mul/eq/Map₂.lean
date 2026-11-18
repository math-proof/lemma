module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic.Part2
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path]
public theorem Vector.Mul.eq.Map₂
  [Mul α]
  (a b : List.Vector α n) :
  a * b = a.map₂ HMul.hMul b :=
  rfl
