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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part32


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def zeroTableClosedBallRGPackage_radiusFive :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  zeroTableClosedBallRGPackage.with_larger_closedBallRadius
    (radius' := 5)
    (by
      norm_num [zeroTableClosedBallRGPackage,
        halfThirdScalingUnitClosedBallRGPackage,
        halfThirdScalingUnitClosedBallCertificate,
        FinitePlusTailClosedBallContractionCertificate.ofResidualMargin,
        FinitePlusTailClosedBallContractionCertificate.ofResidualBound])


end FinitePlusTailContractionExample
end Exact3D
end StatMech
