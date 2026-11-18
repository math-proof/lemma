module

public import Def.Data.Tensor.Defs.Part4
public import Instance.Data.Tensor.Defs.Part2

public section


public theorem Tensor.DataNeg.eq.NegData
  [Neg α]
-- given
  (X : Tensor α s) :
-- imply
  (-X).data = -X.data :=
-- proof
  rfl


-- created on 2025-10-04
