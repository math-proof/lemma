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
import Instance.v1.Atlas.EllipticCurves.code.Theorem151
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The uniformization map on a non-lattice point: send `z ∉ L` to the affine
point `(℘(z), ℘'(z)/2)` of `E_L`. -/
def PhiAux (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) : L.ELPoint :=
  WeierstrassCurve.Affine.Point.some
    (L.weierstrassPFun z) (L.derivWeierstrassPFun z / 2)
    (L.weierstrassP_point_nonsingular z hz)

end ComplexLattice
end
