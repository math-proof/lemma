import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Candido polynomial identity

This module formalizes the Candido polynomial identity.
-/

namespace MetaMathlibExt

/-- Candido polynomial identity:
`2 * (x ^ 4 + y ^ 4 + (x + y) ^ 4) = (x ^ 2 + y ^ 2 + (x + y) ^ 2) ^ 2`,
valid over any commutative semiring. -/
theorem candido_identity {R : Type*} [CommSemiring R] (x y : R) :
    2 * (x ^ 4 + y ^ 4 + (x + y) ^ 4) = (x ^ 2 + y ^ 2 + (x + y) ^ 2) ^ 2 := by
  ring

end MetaMathlibExt
