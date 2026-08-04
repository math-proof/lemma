import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.GeFloor.is.Ge |
| comm | Int.Ge.is.GeFloor |
| mp | Int.Ge.of.GeFloor |
| mpr | Int.GeFloor.of.Ge |
-/
@[main, comm, mp, mpr]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α)
  (n : ℤ) :
-- imply
  ⌊x⌋ ≥ n ↔ x ≥ n :=
-- proof
  Int.le_floor


-- created on 2025-05-05
