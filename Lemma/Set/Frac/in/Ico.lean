import sympy.sets.sets
import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  fract x ∈ Ico 0 1 := by
-- proof
  -- Use the property of the floor function to derive the bounds for the fractional part.
  rw [Set.mem_Ico]
  constructor
  -- Show that the fractional part is non-negative.
  exact Int.fract_nonneg x
  -- Show that the fractional part is less than 1.
  exact Int.fract_lt_one x


-- created on 2025-04-04
