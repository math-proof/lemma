/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part9


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace ClosedBallContractionCertificate

variable {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ}


theorem mapsClosedBall (C : ClosedBallContractionCertificate F) :
    MapsClosedBall F C.center C.radius :=
  mapsClosedBall_of_residual_and_lipschitz F C.center C.c_nonneg C.lipschitz
    C.residual_bound


theorem center_mem (C : ClosedBallContractionCertificate F) :
    ClosedBall C.center C.radius C.center :=
  center_mem_closedBall C.center C.radius_nonneg


theorem residual_l1Dist_le_margin
    (C : ClosedBallContractionCertificate F) :
    l1Dist (F C.center) C.center ≤ (1 - C.c) * C.radius :=
  C.residual_bound


theorem residual_plus_mul_le_radius
    (C : ClosedBallContractionCertificate F) :
    l1Dist (F C.center) C.center + C.c * C.radius ≤ C.radius := by
  calc
    l1Dist (F C.center) C.center + C.c * C.radius ≤
        (1 - C.c) * C.radius + C.c * C.radius := by
      exact add_le_add C.residual_l1Dist_le_margin (le_refl (C.c * C.radius))
    _ = C.radius := by ring


end ClosedBallContractionCertificate
end FiniteContraction
end Exact3D
end StatMech
