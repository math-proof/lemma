module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm, mp, mpr]
public theorem Int.EqFloor.is.Le.Lt
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (a : α)
  (z : ℤ) :
-- imply
  ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < ↑z + 1 :=
-- proof
  Int.floor_eq_iff


public theorem Int.EqFloor.of.Le.Lt
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a : α} {z : ℤ}
  (h1 : ↑z ≤ a)
  (h2 : a < ↑z + 1) :
  ⌊a⌋ = z :=
  (Int.EqFloor.is.Le.Lt a z).mpr ⟨h1, h2⟩

-- created on 2025-03-20
