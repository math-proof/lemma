module

public import Def.Data.Tensor.Defs.Part4
public import Instance.Data.Tensor.Defs.Part2

public section


public theorem Tensor.DataInv.eq.InvData
  [Inv α]
-- given
  (X : Tensor α s) :
-- imply
  X⁻¹.data = X.data⁻¹ :=
-- proof
  rfl


-- created on 2025-10-04
