import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LeCeil.is.Le |
| comm | Int.Le.is.LeCeil |
| mp | Int.Le.of.LeCeil |
| mpr | Int.LeCeil.of.Le |
-/
@[main, comm, mp, mpr]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α)
  (n : ℤ) :
-- imply
  ⌈x⌉ ≤ n ↔ x ≤ n :=
-- proof
  Int.ceil_le


-- created on 2025-05-05
