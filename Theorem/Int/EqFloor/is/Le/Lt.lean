module

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


-- created on 2025-03-20
