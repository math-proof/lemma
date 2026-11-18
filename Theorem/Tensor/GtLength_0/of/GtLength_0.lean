module

public import Def.Data.Tensor.Defs
public import Def.Data.Tensor.Defs.Part4

public section


public theorem Tensor.GtLength_0.of.GtLength_0
  {X : Tensor α s}
-- given
  (h : X.length > 0) :
-- imply
  s.length > 0 := by
-- proof
  by_contra h'
  simp at h'
  simp [Tensor.length] at h
  cases s
  contradiction
  simp_all


-- created on 2025-06-14
