module

public import Initialize.Tactic.Attr.Basic
public import Def.Data.Tensor.Defs
public import Def.Data.Tensor.Defs.Part4
public import Theorem.Tensor.Length.eq.Get_0.of.Ne_Nil
public import Theorem.List.Ne_Nil.is.GtLength_0

public section

open Tensor List


@[comm]
public theorem Tensor.Length.eq.Get_0.of.GtLength_0
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.length = s[0] := by
-- proof
  rw [Length.eq.Get_0.of.Ne_Nil ((List.Ne_Nil.is.GtLength_0 s).mpr h)]
  dsimp only [GetElem.getElem]


-- created on 2025-06-14
-- updated on 2026-10-26
