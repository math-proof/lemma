module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Int.LeCeil.is.Le |
| comm | Int.Le.is.LeCeil |
| mp | Int.Le.of.LeCeil |
| mpr | Int.LeCeil.of.Le |
-/
@[comm, mp, mpr]
public theorem Int.LeCeil.is.Le
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α)
  (n : ℤ) :
-- imply
  ⌈x⌉ ≤ n ↔ x ≤ n :=
-- proof
  Int.ceil_le



public theorem Int.LeCeil.of.Le
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} {n : ℤ} (h : x ≤ n) : ⌈x⌉ ≤ n :=
  (Int.LeCeil.is.Le x n).mpr h

-- created on 2025-05-05
