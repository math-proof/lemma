module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm, mp, mpr]
public theorem Rat.GeInv_0.is.Ge_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
-- given
  (a : α) :
-- imply
  a⁻¹ ≥ 0 ↔ a ≥ 0 :=
-- proof
  inv_nonneg



public theorem Rat.GeInv_0.of.Ge_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {a : α} (h : a ≥ 0) : a⁻¹ ≥ 0 :=
  (Rat.GeInv_0.is.Ge_0 a).mpr h

-- created on 2025-01-14
