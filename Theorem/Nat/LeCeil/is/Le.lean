module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Int.LeCeil.is.Le

public section

open Int


@[comm, mp, mpr]
public theorem Nat.LeCeil.is.Le
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α)
  (n : ℕ) :
-- imply
  ⌈x⌉ ≤ n ↔ x ≤ n := by
-- proof
  simp [Int.LeCeil.is.Le]



public theorem Nat.LeCeil.of.Le
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} {n : ℕ} (h : x ≤ n) : ⌈x⌉ ≤ n :=
  (Nat.LeCeil.is.Le x n).mpr h

-- created on 2025-11-08
