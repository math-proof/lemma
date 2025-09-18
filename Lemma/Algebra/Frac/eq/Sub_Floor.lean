import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  fract x = x - ⌊x⌋ :=
-- proof
  rfl


-- created on 2025-03-04
