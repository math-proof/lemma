import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Ceil.eq.AddFloor_1.is.NotIn_Range |
| comm | Set.NotIn_Range.is.Ceil.eq.AddFloor_1 |
| mp | Set.NotIn_Range.of.Ceil.eq.AddFloor_1 |
| mpr | Set.Ceil.eq.AddFloor_1.of.NotIn_Range |
-/
@[main, comm, mp, mpr]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
-- given
  (x : α) :
-- imply
  ⌈x⌉ = ⌊x⌋ + 1 ↔ x ∉ Set.range Int.cast :=
-- proof
  Int.ceil_eq_floor_add_one_iff_notMem x


-- created on 2025-07-31
