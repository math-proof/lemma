module

public import Def.Data.Tensor.Defs.Part4
public import Instance.Data.Tensor.Defs.Part2

public section


public theorem Tensor.EqData0'0
  [Zero α]
-- given
  (s : List ℕ) :
-- imply
  (0 : Tensor α s).data = 0 :=
-- proof
  rfl


-- created on 2025-06-22
