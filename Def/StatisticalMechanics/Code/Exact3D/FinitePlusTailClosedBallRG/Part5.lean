/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part4


namespace StatMech

namespace Exact3D

namespace FinitePlusTailClosedBallRGPackage

variable {n : ℕ} {α : Type}


def with_larger_residual
    (P : FinitePlusTailClosedBallRGPackage n α)
    {residual' : ℝ} (hresidual : P.closedBall.residual ≤ residual')
    (hbudget :
      residual' + P.closedBall.contraction.c * P.closedBall.radius ≤
        P.closedBall.radius) :
    FinitePlusTailClosedBallRGPackage n α where
  closedBall := P.closedBall.with_larger_residual hresidual hbudget
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one

end FinitePlusTailClosedBallRGPackage
end Exact3D
end StatMech
