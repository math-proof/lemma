/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBallRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part2


namespace StatMech

namespace Exact3D

structure FinitePlusTailClosedBallRGPackage (n : ℕ) (α : Type) where
  closedBall : FinitePlusTailClosedBallContractionCertificate n α
  thermal : ℝ
  thermal_gt_one : 1 < thermal

end Exact3D
end StatMech
