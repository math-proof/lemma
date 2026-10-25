/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificateExample.Part3


namespace StatMech

namespace Exact3D

namespace MatrixCertificateExample

theorem stableMatrix_map_zero :
    (fun i => RatInterval.matVec stableMatrix (0 : Fin 2 → ℝ) i) = 0 := by
  funext i
  simp [RatInterval.matVec]


end MatrixCertificateExample
end Exact3D
end StatMech
