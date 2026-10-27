import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Def.AlgebraicGeometry.EllipticCurve.PointCount.Part2
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

theorem frobeniusTrace_eq [Finite F] :
    W.frobeniusTrace = (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ) :=
  rfl

/-- The rational-point count is one plus the number of affine solutions to the Weierstrass
equation; the extra point is the point at infinity. -/
theorem natCard_point_eq_natCard_affineSolutions_add_one [Finite F] [W.IsElliptic] :
    Nat.card W.Point = Nat.card {xy : Prod F F // W.Equation xy.1 xy.2} + 1 := by
  calc
    Nat.card W.Point =
        Nat.card (WithZero {xy : Prod F F // W.Equation xy.1 xy.2}) :=
      Nat.card_congr W.pointEquiv
    _ = Nat.card {xy : Prod F F // W.Equation xy.1 xy.2} + 1 := by
      change Nat.card (Option {xy : Prod F F // W.Equation xy.1 xy.2}) = _
      exact Finite.card_option

end WeierstrassCurve.Affine
