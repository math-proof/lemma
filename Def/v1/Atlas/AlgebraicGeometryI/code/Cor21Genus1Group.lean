/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Cor21Genus1Group.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
set_option maxHeartbeats 400000


noncomputable section

/-- The arithmetic genus of any affine Weierstrass curve, fixed at `1`. -/
def WeierstrassCurve.Affine.arithmeticGenus {F : Type*} [Field F]
    (_ : WeierstrassCurve.Affine F) : ℕ := 1

end
