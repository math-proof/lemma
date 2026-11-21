module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path]
private theorem main
  [Div α]
-- given
  (a b : List.Vector α n) :
-- imply
  a / b = a.map₂ HDiv.hDiv b :=
-- proof
  rfl


-- created on 2025-09-23
