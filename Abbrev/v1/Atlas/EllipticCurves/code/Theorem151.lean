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
import Def.v1.Atlas.EllipticCurves.code.Theorem151
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The type of points on the elliptic curve `E_L` associated to the lattice `L`. -/
abbrev ELPoint : Type := L.ellipticCurveEL_affine.Point

end ComplexLattice
end
