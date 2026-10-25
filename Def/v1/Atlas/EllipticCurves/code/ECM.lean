/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.IntegerFactorization.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IntegerFactorization


noncomputable section

open Nat Finset

/-- The short Weierstrass curve `y² = x³ + a x + b` over a commutative ring `R`,
represented as a `WeierstrassCurve` with `a₁ = a₂ = a₃ = 0`, `a₄ = a` and `a₆ = b`. -/
def shortWeierstrass {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, a, b⟩

/-- The discriminant quantity `4 a³ + 27 b²` of the short Weierstrass curve
`y² = x³ + a x + b`, used by ECM (Algorithm 10.11) to detect a nontrivial gcd with `N`. -/
def ecmDiscriminant {R : Type*} [CommRing R] (a b : R) : R :=
  4 * a ^ 3 + 27 * b ^ 2

end
