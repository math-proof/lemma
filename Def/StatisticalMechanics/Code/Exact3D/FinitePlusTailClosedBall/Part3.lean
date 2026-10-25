/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part2


namespace StatMech

namespace Exact3D

open scoped NNReal


namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}


def with_larger_residual
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    FinitePlusTailClosedBallContractionCertificate n α where
  contraction := C.contraction
  center := C.center
  radius := C.radius
  residual := residual'
  radius_nonneg := C.radius_nonneg
  residual_bound := le_trans C.residual_bound hresidual
  radius_bound := hbudget

end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
