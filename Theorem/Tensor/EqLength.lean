module

public import Initialize.Tactic.Attr.Basic
public import Def.Data.Tensor.Defs
public import Def.Data.Tensor.Defs.Part4

public section


@[grind =]
public theorem Tensor.EqLength
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.length = n := by
-- proof
  simp [Tensor.length]


-- created on 2025-12-08
