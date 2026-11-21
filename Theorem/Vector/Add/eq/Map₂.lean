module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic

public section


@[path]
public theorem Vector.Add.eq.Map₂
  [Add α]
  (a b : List.Vector α n) :
  a + b = a.map₂ HAdd.hAdd b :=
  rfl
