import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorem.AlgebraicGeometry.EllipticCurve.ManinSequence
/-!
# Integer sequences in Manin's proof

This file contains the elementary arithmetic at the end of Manin's proof of the Hasse bound.
-/


namespace AlgebraicGeometry.EllipticCurve

/-- The four properties of the polynomial-degree sequence used in Manin's proof. -/
structure ManinDegreeData (q N : ℕ) where
  /-- The numerator degree attached to the point indexed by an integer. -/
  d : ℤ → ℕ
  /-- Frobenius has degree `q`. -/
  zero : d 0 = q
  /-- Frobenius minus the identity has degree equal to the rational point count. -/
  negOne : d (-1) = N
  /-- The degree sequence has constant second difference two. -/
  recurrence : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2
  /-- Consecutive points in the sequence cannot both have degree zero. -/
  noAdjacentZeros : ∀ n, d n = 0 → d (n + 1) = 0 → False

end AlgebraicGeometry.EllipticCurve
