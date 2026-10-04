import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α) :
-- imply
  ∃ n : ℤ, (n : α) ∈ Set.Ioc (x - 1) x := by
-- proof
  refine ⟨⌊x⌋, Set.mem_Ioc.mpr ⟨?_, ?_⟩⟩
  · exact sub_lt_iff_lt_add.mpr (Int.lt_floor_add_one x)
  · exact Int.floor_le x


-- created on 2021-04-21
