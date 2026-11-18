module

public import Def.Data.Tensor.Defs.Part4
public import Instance.Data.Tensor.Defs.Part2

public section


public theorem Tensor.DataAdd.eq.AddDataS
  [Add α]
-- given
  (A B : Tensor α s) :
-- imply
  (A + B).data = A.data + B.data :=
-- proof
  rfl


-- created on 2025-06-22
