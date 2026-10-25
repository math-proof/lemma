/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/SurfaceTensionConvexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech

namespace Exact3D

abbrev SurfaceVec3 : Type :=
  Fin 3 → ℝ


end Exact3D
end StatMech
