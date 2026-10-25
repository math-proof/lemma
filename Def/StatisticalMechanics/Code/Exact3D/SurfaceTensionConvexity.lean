/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/SurfaceTensionConvexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity


namespace StatMech

namespace Exact3D

def surfaceVec3 (x y z : ℝ) : SurfaceVec3 :=
  ![x, y, z]


def surfaceXAxisUnit : SurfaceVec3 :=
  surfaceVec3 1 0 0


end Exact3D
end StatMech
