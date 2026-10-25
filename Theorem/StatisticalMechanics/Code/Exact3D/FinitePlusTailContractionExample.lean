/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContractionExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample.Part7
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingCertificate_c_eq :
    halfThirdScalingCertificate.c = (1 : ℝ) / 2 := by
  rfl


theorem halfThirdScalingCertificate_mixed_lipschitz
    (x y : FinitePlusTailState 1 ℕ) :
    (halfThirdScalingCertificate.map x).dist
        (halfThirdScalingCertificate.map y) ≤
      ((1 : ℝ) / 2) * x.dist y := by
  simpa [halfThirdScalingCertificate_c_eq] using
    halfThirdScalingCertificate.mixed_lipschitz x y


theorem halfThirdScalingCertificate_c_lt_one :
    halfThirdScalingCertificate.c < 1 := by
  simpa [halfThirdScalingCertificate_c_eq] using
    halfThirdScalingCertificate.c_lt_one


end FinitePlusTailContractionExample
end Exact3D
end StatMech
