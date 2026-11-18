module

public import Initialize.Tactic.Attr.Basic
public import Def.Data.Tensor.Defs
public import Def.Data.Tensor.Defs.Part4

public section


@[grind =]
public theorem Tensor.LengthMap.eq.Length
-- given
  (X : Tensor α s)
  (f : α → β) :
-- imply
  (X.map f).length = X.length := by
-- proof
  unfold Tensor.length
  aesop


-- created on 2025-12-23
