import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Theorem.AlgebraicGeometry.EllipticCurve.PointCount.Part2
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

def affineSolutionsEquivSigma :
    {xy : Prod F F // W.Equation xy.1 xy.2} ≃ Σ x : F, {y : F // W.Equation x y} where
  toFun xy := ⟨xy.1.1, xy.1.2, xy.2⟩
  invFun xy := ⟨(xy.1, xy.2.1), xy.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end WeierstrassCurve.Affine
