module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path]
public theorem Vector.One.eq.Replicate
  [One α] :
  (1 : List.Vector α n) = List.Vector.replicate n 1 :=
  rfl
