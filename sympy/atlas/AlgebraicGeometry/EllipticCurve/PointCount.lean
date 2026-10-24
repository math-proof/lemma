/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Point counts of elliptic curves over finite fields

This file defines the Frobenius trace of an elliptic curve over a finite field through its rational
point count. It also supplies a finiteness instance for the canonical affine point type.
-/

open Polynomial

namespace WeierstrassCurve.Affine

universe u

variable {R : Type u} [CommRing R] (W : Affine R)

namespace Point

/-- The nonsingular points of a Weierstrass curve over a finite commutative ring form a finite
type. The point at infinity is included. -/
instance instFinitePoint [Finite R] : Finite W.Point := by
  let _ : Finite (WithZero {xy : R × R // W.Nonsingular xy.1 xy.2}) :=
    inferInstanceAs (Finite (Option {xy : R × R // W.Nonsingular xy.1 xy.2}))
  exact Finite.of_injective W.nonsingularPointEquiv W.nonsingularPointEquiv.injective

end Point

variable {F : Type u} [Field F]

/-- The Frobenius trace of an elliptic curve over a finite field, defined by
`a_q(E) = q + 1 - #E(𝔽_q)`. The point at infinity belongs to `W.Point`. -/
noncomputable def frobeniusTrace (W : Affine F) [Finite F] : ℤ :=
  (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ)

variable (W : Affine F)

private noncomputable def equationPolynomial (x : F) : F[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

private def affineSolutionsEquivSigma :
    {xy : F × F // W.Equation xy.1 xy.2} ≃ Σ x : F, {y : F // W.Equation x y} where
  toFun xy := ⟨xy.1.1, xy.1.2, xy.2⟩
  invFun xy := ⟨(xy.1, xy.2.1), xy.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
end WeierstrassCurve.Affine
