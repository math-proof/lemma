/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall


namespace StatMech

namespace Exact3D

open scoped NNReal


namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}


theorem residual_plus_mul_le_radius
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    C.residual + C.contraction.c * C.radius ≤ C.radius :=
  C.radius_bound


theorem mapsClosedBall
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState.MapsClosedBall
      C.contraction.map C.center C.radius :=
  C.contraction.mapsClosedBall_of_residual_and_lipschitz
    C.center C.residual_bound C.residual_plus_mul_le_radius


theorem center_mem
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState.ClosedBall C.center C.radius C.center :=
  FinitePlusTailState.center_mem_closedBall C.center C.radius_nonneg


end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
