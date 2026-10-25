/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.WeierstrassP
import Lemma.Complex.Atlas.v1.EllipticCurves.code.WeierstrassP
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The Weierstrass curve `E_L : y^2 = 4x^3 - g₂(L)·x - g₃(L)` associated to a
lattice `L`, presented in long Weierstrass form with coefficients
`(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, -g₂/4, -g₃/4)`. -/
def ellipticCurveEL : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(L.g₂ / 4), -(L.g₃ / 4)⟩

/-- The affine model of `ellipticCurveEL L`, used to talk about its affine
`Point` type. -/
def ellipticCurveEL_affine : WeierstrassCurve.Affine ℂ :=
  L.ellipticCurveEL.toAffine

end ComplexLattice
end
