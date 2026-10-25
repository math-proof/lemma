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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part22


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


noncomputable def halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs :
    RGCertificate.AnalyticPrefactorBridgeInputs
      halfThirdScalingBlockRGCertificate halfThirdScalingCorrelationLength
      halfThirdScalingPrefactor
      halfThirdScalingToyRGCovariance
      halfThirdScalingToyStableManifoldControl
      halfThirdScalingToyMicroscopicOrbitEntry
      halfThirdScalingToySubcriticalMassBridge :=
  RGCertificate.AnalyticPrefactorBridgeInputs.congr_predictedExponent
    halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


end FinitePlusTailContractionExample
end Exact3D
end StatMech
