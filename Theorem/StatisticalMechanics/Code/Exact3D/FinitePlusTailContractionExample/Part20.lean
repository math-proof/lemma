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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part20


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingBlockRGPackage_relaxedConstants_c :
    halfThirdScalingBlockRGPackage_relaxedConstants.c = (3 : ℝ) / 4 :=
  rfl


theorem halfThirdScalingBlockRGPackage_relaxedConstants_certificate_eq :
    halfThirdScalingBlockRGPackage_relaxedConstants.certificate
      halfThirdScalingBlockScale halfThirdScalingModel =
        halfThirdScalingBlockRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel :=
  rfl


theorem halfThirdScalingBlockRGPackage_relaxedConstants_predictedExponent_eq :
    (halfThirdScalingBlockRGPackage_relaxedConstants.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 :=
  halfThirdScalingBlockRGPackage_relaxedConstants.certificate_predictedExponent_eq
    halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingBlockRGPackage_relaxedConstants_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        (halfThirdScalingBlockRGPackage.certificate
          halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent) :
    HasCriticalNu halfThirdScalingModel correlationLength
      (halfThirdScalingBlockRGPackage_relaxedConstants.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingBlockRGPackage_relaxedConstants] using
    halfThirdScalingBlockRGPackage.with_larger_constants_hasCriticalNu
      (finiteToFinite' := (1 : ℝ) / 2)
      (tailToFinite' := 0)
      (finiteToTail' := 0)
      (tailToTail' := (1 : ℝ) / 2)
      (c' := (3 : ℝ) / 4)
      (by
        norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
          FinitePlusTailBlockBounds.decoupledScaling,
          FinitePlusTailBlockBounds.ofDecoupled])
      (by
        norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
          FinitePlusTailBlockBounds.decoupledScaling,
          FinitePlusTailBlockBounds.ofDecoupled])
      (by
        norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
          FinitePlusTailBlockBounds.decoupledScaling,
          FinitePlusTailBlockBounds.ofDecoupled])
      (by
        norm_num [halfThirdScalingBlockRGPackage, halfThirdScalingBlockBounds,
          FinitePlusTailBlockBounds.decoupledScaling,
          FinitePlusTailBlockBounds.ofDecoupled])
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num [halfThirdScalingBlockRGPackage])
      halfThirdScalingBlockScale halfThirdScalingModel hν


end FinitePlusTailContractionExample
end Exact3D
end StatMech
