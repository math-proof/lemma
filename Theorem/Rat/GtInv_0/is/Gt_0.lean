module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


/--
This lemma establishes that in a group with zero `α` equipped with a partial order and satisfying `ZeroLEOneClass` and `PosMulReflectLT`, the inverse of an element `x` is positive if and only if `x` itself is positive.
It serves as a simplification rule to handle inequalities involving inverses in ordered algebraic structures.
-/
@[comm, mp, mpr]
public theorem Rat.GtInv_0.is.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α} :
-- imply
  x⁻¹ > 0 ↔ x > 0 :=
-- proof
  inv_pos



public theorem Rat.GtInv_0.of.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α} (h : x > 0) : x⁻¹ > 0 :=
  (Rat.GtInv_0.is.Gt_0).mpr h

-- created on 2024-11-25
-- updated on 2026-10-26
