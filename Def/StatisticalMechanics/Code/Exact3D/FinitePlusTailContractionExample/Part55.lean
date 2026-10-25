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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part53


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def genCubicClassReplacedInfiniteTailPackage :
    InfiniteTailTableWitnessPackage
      (Case := BoundedPolymerCase.CubicClass 1
        tableClosedBallCouplingCutoff.radius
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (α := FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  generatedCubicClassInfiniteTailPackage_replacedTailEnvelope
    (d := 1)
    tableClosedBallCouplingCutoff
    genCubicClassEmptySupport
    genCubicClassEmptySupport_saturated


end FinitePlusTailContractionExample
end Exact3D
end StatMech
