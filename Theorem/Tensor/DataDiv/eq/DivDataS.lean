module

public import Def.Data.Tensor.Defs.Part4
public import Instance.Data.Tensor.Defs.Part2

public section


public theorem Tensor.DataDiv.eq.DivDataS
  [Div α]
-- given
  (X Y : Tensor α s) :
-- imply
  (X / Y).data = X.data / Y.data := by
-- proof
  aesop


-- created on 2025-09-21
-- updated on 2026-10-26
