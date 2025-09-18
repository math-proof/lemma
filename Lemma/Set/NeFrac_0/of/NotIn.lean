import sympy.functions.elementary.integers
import Lemma.Set.In_Range.of.EqFrac_0
open Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∉ Set.range Int.cast) :
-- imply
  fract x ≠ 0 := by
-- proof
  by_contra h'
  have := In_Range.of.EqFrac_0 h'
  contradiction


-- created on 2025-04-04
