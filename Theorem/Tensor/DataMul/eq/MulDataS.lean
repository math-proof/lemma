module

public import Def.Data.Tensor.Defs.Part4
public import Instance.Data.Tensor.Defs.Part2

public section


public theorem Tensor.DataMul.eq.MulDataS
  [Mul α]
-- given
  (A B : Tensor α s) :
-- imply
  (A * B).data = A.data * B.data :=
-- proof
  rfl


-- created on 2025-05-02
-- updated on 2026-10-26
