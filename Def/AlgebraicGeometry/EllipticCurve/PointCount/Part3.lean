import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Theorem.AlgebraicGeometry.EllipticCurve.PointCount
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

variable (W : Affine F)

noncomputable def equationPolynomial (x : F) : F[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

end WeierstrassCurve.Affine
