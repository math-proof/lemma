/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean -/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
open Polynomial

/-!
# Point counts of elliptic curves over finite fields

This file defines the Frobenius trace of an elliptic curve over a finite field through its rational
point count. It also supplies a finiteness instance for the canonical affine point type.
-/


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
end WeierstrassCurve.Affine
