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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part21


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingBlockRGCertificate_fixedPointEnclosure :
    halfThirdScalingBlockRGCertificate.FixedPointEnclosure := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_fixedPointEnclosure
      halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingBlockRGCertificate_hyperbolicSplitting :
    halfThirdScalingBlockRGCertificate.HyperbolicSplitting :=
  halfThirdScalingBlockRGCertificate.hyperbolicSplitting_of_thermal_gt_one


theorem halfThirdScalingBlockRGCertificate_linearizationEnclosure :
    halfThirdScalingBlockRGCertificate.LinearizationEnclosure :=
  halfThirdScalingBlockRGCertificate.linearizationEnclosure_of_thermal_gt_one


theorem halfThirdScalingBlockRGCertificate_cone_iterate
    {η : ℝ} (hη : 0 ≤ η)
    {x : halfThirdScalingBlockRGCertificate.H.carrier}
    (hx : halfThirdScalingBlockRGPackage.hyperbolicSplitting.cone η x)
    (k : ℕ) :
    halfThirdScalingBlockRGPackage.hyperbolicSplitting.cone η
      (((halfThirdScalingBlockRGCertificate.R.map)^[k]) x) := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_cone_iterate
      halfThirdScalingBlockScale halfThirdScalingModel hη hx k


theorem halfThirdScalingBlockRGCertificate_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingBlockRGCertificate.RGToExponentBridge correlationLength) :
    halfThirdScalingBlockRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_valid_of_bridge
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hbridge


theorem halfThirdScalingBlockRGCertificate_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingBlockRGCertificate.RGToExponentBridge correlationLength) :
    HasCriticalNu halfThirdScalingModel correlationLength
      halfThirdScalingBlockRGCertificate.predictedExponent :=
  (halfThirdScalingBlockRGCertificate_valid_of_bridge
    correlationLength hbridge).hasCriticalNu


theorem halfThirdScalingBlockRGCertificate_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingBlockRGCertificate.predictedExponent) :
    halfThirdScalingBlockRGCertificate.RGToExponentBridge
      correlationLength := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_rgToExponentBridge_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν


theorem halfThirdScalingBlockRGCertificate_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingBlockRGCertificate.predictedExponent) :
    halfThirdScalingBlockRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGPackage.certificate_valid_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν


theorem halfThirdScalingBlockRGCertificate_predictedExponent_eq_rg :
    halfThirdScalingBlockRGCertificate.predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  calc
    halfThirdScalingBlockRGCertificate.predictedExponent =
        predictedNu halfThirdScalingBlockScale 3 := by
      simpa [halfThirdScalingBlockRGCertificate] using
        halfThirdScalingBlockRGPackage_predictedExponent_eq
    _ = halfThirdScalingRGCertificate.predictedExponent := by
      symm
      exact halfThirdScalingRGCertificate_predictedExponent_eq


end FinitePlusTailContractionExample
end Exact3D
end StatMech
