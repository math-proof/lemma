module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path]
private theorem main
  [Mul α]
-- given
  (a b : List.Vector α n) :
-- imply
  a * b = a.map₂ HMul.hMul b :=
-- proof
  rfl


-- created on 2025-06-22
