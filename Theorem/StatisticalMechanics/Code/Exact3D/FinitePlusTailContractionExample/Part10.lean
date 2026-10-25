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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part10


namespace StatMech

namespace Exact3D

namespace FinitePlusTailContractionExample

open InfiniteTailStableKeyPackageExample

open InfiniteTailGeneratedTablePackageExample

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingRGCertificate_fixedPointEnclosure :
    halfThirdScalingRGCertificate.FixedPointEnclosure := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_fixedPointEnclosure
      halfThirdScalingBlockScale halfThirdScalingModel


theorem halfThirdScalingRGCertificate_hyperbolicSplitting :
    halfThirdScalingRGCertificate.HyperbolicSplitting :=
  halfThirdScalingRGCertificate.hyperbolicSplitting_of_thermal_gt_one


theorem halfThirdScalingRGCertificate_linearizationEnclosure :
    halfThirdScalingRGCertificate.LinearizationEnclosure :=
  halfThirdScalingRGCertificate.linearizationEnclosure_of_thermal_gt_one


theorem halfThirdScalingRGCertificate_predictedExponent_eq :
    halfThirdScalingRGCertificate.predictedExponent =
      predictedNu halfThirdScalingBlockScale 3 :=
  rfl


theorem halfThirdScalingRGCertificate_cone_iterate
    {η : ℝ} (hη : 0 ≤ η)
    {x : halfThirdScalingRGCertificate.H.carrier}
    (hx : halfThirdScalingHyperbolicSplitting.cone η x)
    (k : ℕ) :
    halfThirdScalingHyperbolicSplitting.cone η
      (((halfThirdScalingRGCertificate.R.map)^[k]) x) := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_cone_iterate
      halfThirdScalingBlockScale halfThirdScalingModel hη hx k


theorem halfThirdScalingRGCertificate_valid_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingRGCertificate.RGToExponentBridge correlationLength) :
    halfThirdScalingRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_valid_of_bridge
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hbridge


theorem halfThirdScalingRGCertificate_hasCriticalNu_of_bridge
    (correlationLength : ℝ → ℝ)
    (hbridge :
      halfThirdScalingRGCertificate.RGToExponentBridge correlationLength) :
    HasCriticalNu halfThirdScalingModel correlationLength
      halfThirdScalingRGCertificate.predictedExponent :=
  (halfThirdScalingRGCertificate_valid_of_bridge
    correlationLength hbridge).hasCriticalNu


theorem halfThirdScalingRGCertificate_rgToExponentBridge_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingRGCertificate.predictedExponent) :
    halfThirdScalingRGCertificate.RGToExponentBridge correlationLength := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_rgToExponentBridge_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν


theorem halfThirdScalingRGCertificate_valid_of_hasCriticalNu
    (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu halfThirdScalingModel correlationLength
        halfThirdScalingRGCertificate.predictedExponent) :
    halfThirdScalingRGCertificate.Valid correlationLength := by
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingHyperbolicSplitting.certificate_valid_of_hasCriticalNu
      halfThirdScalingBlockScale halfThirdScalingModel correlationLength hν


end FinitePlusTailContractionExample
end Exact3D
end StatMech
