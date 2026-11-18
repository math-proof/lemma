module

public import Initialize.Tactic.Attr.Basic
public import Def.Data.Tensor.Defs
public import Def.Data.Tensor.Defs.Part4
public import Theorem.List.Ne_Nil.is.GtLength_0

public section

open List


@[comm]
public theorem Tensor.Length.eq.Get_0.of.Ne_Nil
-- given
  (h : s ≠ [])
  (X : Tensor α s) :
-- imply
  X.length = s.get ⟨0, GtLength_0.of.Ne_Nil h⟩ := by
-- proof
  simp [Tensor.length]
  cases s
  ·
    contradiction
  ·
    cases X
    simp


-- created on 2025-10-10
