import sympy.functions.elementary.integers
import Lemma.Set.In_Range.is.Any_EqUFn
import Lemma.Algebra.Frac.eq.Sub_Floor
import Lemma.Algebra.Sub.eq.Zero.is.Eq
open Set Algebra


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
  simp [In_Range.is.Any_EqUFn]
  use ⌊x⌋
  apply Eq.symm
  apply Eq.of.Sub.eq.Zero
  rw [← Frac.eq.Sub_Floor]
  assumption


-- created on 2025-04-04
