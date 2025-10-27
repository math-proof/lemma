import sympy.functions.elementary.integers
import Lemma.Set.In_Range.is.Any_EqUFn
import Lemma.Rat.Frac.eq.Sub_Floor
import Lemma.Int.Sub.eq.Zero.is.Eq
open Set Int Rat


/--
If the fractional part of a real number `x` is zero, then `x` is an integer.
This lemma establishes that `x` belongs to the range of the integer embedding in the field `α`, leveraging the property that the fractional part `fract x` equals `x - ⌊x⌋` and the given condition `fract x = 0`.
-/
@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : fract x = 0) :
-- imply
  x ∈ Set.range Int.cast := by
-- proof
  use ⌊x⌋
  apply Eq.symm
  apply Eq.of.Sub.eq.Zero
  rwa [← Frac.eq.Sub_Floor]


-- created on 2025-04-04
