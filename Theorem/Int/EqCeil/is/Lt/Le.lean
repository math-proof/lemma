module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public section


@[comm, mp, mpr]
public theorem Int.EqCeil.is.Lt.Le
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (a : α)
  (z : ℤ) :
-- imply
  ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ ↑z :=
-- proof
  Int.ceil_eq_iff



public theorem Int.EqCeil.of.Lt.Le
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a : α} {z : ℤ}
  (h₀ : ↑z - 1 < a)
  (h₁ : a ≤ ↑z) :
  ⌈a⌉ = z :=
  (Int.EqCeil.is.Lt.Le a z).mpr ⟨h₀, h₁⟩

-- created on 2025-03-20
