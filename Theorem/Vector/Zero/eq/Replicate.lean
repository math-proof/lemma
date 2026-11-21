module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path, comm]
private theorem main
  [Zero α] :
-- imply
  (0 : List.Vector α n) = List.Vector.replicate n 0 :=
-- proof
  rfl


-- created on 2025-06-22
