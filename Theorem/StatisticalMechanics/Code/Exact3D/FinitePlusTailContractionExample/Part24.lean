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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part24


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingBlockRGCertificate_bridge_from_massInputs :
    halfThirdScalingBlockRGCertificate.RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticMassBridgeInputs.rgToExponentBridge
    halfThirdScalingBlockRGAnalyticMassBridgeInputs


theorem halfThirdScalingBlockRGCertificate_valid_from_massInputs :
    halfThirdScalingBlockRGCertificate.Valid halfThirdScalingCorrelationLength :=
  RGCertificate.AnalyticMassBridgeInputs.valid_of_checks
    halfThirdScalingBlockRGAnalyticMassBridgeInputs
    trivial trivial halfThirdScalingBlockRGCertificate_fixedPointEnclosure
    halfThirdScalingBlockRGCertificate_linearizationEnclosure
    halfThirdScalingBlockRGCertificate_hyperbolicSplitting trivial


theorem halfThirdScalingBlockRGCertificate_hasCriticalNu_from_massInputs :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      halfThirdScalingBlockRGCertificate.predictedExponent :=
  RGCertificate.AnalyticMassBridgeInputs.hasCriticalNu
    halfThirdScalingBlockRGAnalyticMassBridgeInputs


theorem halfThirdScalingCertificate_zero_residual :
    (halfThirdScalingCertificate.map zeroState).dist zeroState ≤ 0 := by
  rw [halfThirdScalingCertificate_map_zero, FinitePlusTailState.dist_self]


theorem halfThirdScalingCertificate_unitCenter_residual :
    (halfThirdScalingCertificate.map unitCenterState).dist unitCenterState ≤
      (1 : ℝ) / 2 := by
  norm_num [unitCenterState, halfThirdScalingCertificate,
    FinitePlusTailLipschitzCertificate.decoupledScaling,
    FinitePlusTailLipschitzCertificate.ofDecoupled,
    FinitePlusTailState.dist, FiniteContraction.l1Dist,
    RatInterval.supNormVec, SummableTail.dist, SummableTail.scale]


theorem halfThirdScalingCertificate_fixedPoint_eq_zero :
    halfThirdScalingCertificate.fixedPoint = zeroState := by
  symm
  exact halfThirdScalingCertificate.eq_fixedPoint_of_isFixed
    halfThirdScalingCertificate_map_zero


theorem halfThirdScalingCertificate_exists_unique_fixedPoint :
    ∃! p : FinitePlusTailState 1 ℕ,
      halfThirdScalingCertificate.map p = p :=
  halfThirdScalingCertificate.exists_unique_fixedPoint


theorem halfThirdScalingCertificate_mapsClosedBall_zero {radius : ℝ}
    (hradius : 0 ≤ radius) :
    FinitePlusTailState.MapsClosedBall
      halfThirdScalingCertificate.map zeroState radius := by
  apply halfThirdScalingCertificate.mapsClosedBall_of_residual_and_lipschitz
    (center := zeroState) (residual := 0)
  · exact halfThirdScalingCertificate_zero_residual
  · rw [halfThirdScalingCertificate_c_eq]
    nlinarith


end FinitePlusTailContractionExample
end Exact3D
end StatMech
