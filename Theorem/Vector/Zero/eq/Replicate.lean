module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path, comm]
public theorem Vector.Zero.eq.Replicate
  [Zero α] :
  (0 : List.Vector α n) = List.Vector.replicate n 0 :=
  rfl
