import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Order
open scoped ComplexOrder

/-!
# Real-rooted complex polynomials

A complex polynomial is *real-rooted* if every member of its root multiset
is real.  This file defines the predicate `Polynomial.IsRealRooted`, the
auxiliary quantity `Polynomial.maxRealRoot` (the largest real part of a
root, defaulting to zero), and proves that a monic real-rooted polynomial
is positive to the right of its largest root and nonnegative on the
closed half-line to the right of it.
-/


namespace Polynomial

/-- A complex polynomial is real-rooted if every member of its root multiset is real. -/
def IsRealRooted (p : Polynomial ℂ) : Prop :=
  ∀ z ∈ p.roots, z.im = 0

end Polynomial
