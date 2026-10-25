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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part42


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def genMinCubicKeyReplacedTableClosedBallRGPackage :
    @InfiniteTailTableClosedBallRGPackage Unit
      (BoundedPolymerCase.StableKey
        tableClosedBallCouplingCutoff.maxDegree
        tableClosedBallCouplingCutoff.maxRange)
      (FiniteCutoffCoordinate 1 tableClosedBallCouplingCutoff) ℕ _ _
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) 1 :=
  zeroTableClosedBallRGPackage_radiusFive.with_tableWitness_as_closedBallResidual
    genMinCubicKeyReplacedInfiniteTailPackage
    (by
      rw [zeroTableClosedBallRGPackage_radiusFive_residual_eq,
        genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two]
      norm_num)
    (by
      rw [genMinCubicKeyReplacedInfiniteTailPackage_budget_eq_two,
        zeroTableClosedBallRGPackage_radiusFive_contraction_c_eq,
        zeroTableClosedBallRGPackage_radiusFive_radius_eq]
      norm_num)


end FinitePlusTailContractionExample
end Exact3D
end StatMech
