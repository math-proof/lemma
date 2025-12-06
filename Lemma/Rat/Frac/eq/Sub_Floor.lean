import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  (x : α) :
-- imply
  fract x = x - ⌊x⌋ :=
-- proof
  rfl


-- created on 2025-03-04
