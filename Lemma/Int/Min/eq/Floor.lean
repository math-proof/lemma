import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x y : α}
  {n : ℤ} :
-- imply
  min (n + ⌊x⌋) ⌊y⌋ = ⌊min (n + x) y⌋ := by
-- proof
  rw [← Int.floor_intCast_add, Int.floor_mono.map_min]


-- created on 2020-01-25
