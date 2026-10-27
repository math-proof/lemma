import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Instance.AlgebraicGeometry.EllipticCurve.PointCount.Part2
open Polynomial

/-!
# Point counts of elliptic curves over finite fields

This file defines the Frobenius trace of an elliptic curve over a finite field through its rational
point count. It also supplies a finiteness instance for the canonical affine point type.
-/


namespace WeierstrassCurve.Affine

universe u

variable {R : Type u} [CommRing R] (W : Affine R)

variable {F : Type u} [Field F]

/-- The Frobenius trace of an elliptic curve over a finite field, defined by
`a_q(E) = q + 1 - #E(𝔽_q)`. The point at infinity belongs to `W.Point`. -/
noncomputable def frobeniusTrace (W : Affine F) [Finite F] : ℤ :=
  (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ)

end WeierstrassCurve.Affine
