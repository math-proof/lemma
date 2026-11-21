module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path]
private theorem main
  [One α] :
-- imply
  (1 : List.Vector α n) = List.Vector.replicate n 1 :=
-- proof
  rfl


-- created on 2025-09-22
