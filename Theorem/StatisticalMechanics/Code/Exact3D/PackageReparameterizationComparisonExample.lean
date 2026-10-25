/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridge
import Def.StatisticalMechanics.Code.Exact3D.PackageReparameterizationComparisonExample


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationComparisonExample

open FinitePlusTailContractionExample

open FiniteWitnessPackageExample

open PackageReparameterizationBridgeExample

open FinitePlusTailHyperbolicSplitting

open InfiniteTailTableClosedBallRGPackage


theorem halfThirdScalingReparameterizedLength_pos :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      0 < halfThirdScalingReparameterizedLength β :=
  Filter.Eventually.of_forall fun _ => by
    dsimp [halfThirdScalingReparameterizedLength,
      halfThirdScalingCorrelationLength]
    exact Real.exp_pos _


theorem halfThirdScalingDoubledReparameterizedLength_comparable :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      (2 : ℝ) * halfThirdScalingReparameterizedLength β ≤
          halfThirdScalingDoubledReparameterizedLength β ∧
        halfThirdScalingDoubledReparameterizedLength β ≤
          (2 : ℝ) * halfThirdScalingReparameterizedLength β :=
  Filter.Eventually.of_forall fun β => by
    simp [halfThirdScalingDoubledReparameterizedLength,
      halfThirdScalingDoublePrefactor]


theorem halfThirdScalingHyperbolicSplitting_bridge_doubled_reparameterized :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingDoubledReparameterizedLength := by
  have hbridge :
      halfThirdScalingRGCertificate.RGToExponentBridge
        halfThirdScalingReparameterizedLength := by
    simpa using halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized
  simpa [halfThirdScalingRGCertificate] using
    certificate_rgToExponentBridge_of_eventually_const_mul_le_le
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingModel
      hbridge
      halfThirdScalingReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubledReparameterizedLength_comparable


theorem halfThirdScalingHyperbolicSplitting_valid_doubled_reparameterized :
    halfThirdScalingRGCertificate.Valid
      halfThirdScalingDoubledReparameterizedLength := by
  have hbridge :
      halfThirdScalingRGCertificate.RGToExponentBridge
        halfThirdScalingReparameterizedLength := by
    simpa using halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized
  simpa [halfThirdScalingRGCertificate] using
    certificate_valid_of_eventually_const_mul_le_le
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingModel
      hbridge
      halfThirdScalingReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubledReparameterizedLength_comparable


theorem halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_reparameterized :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingDoubledReparameterizedLength
      halfThirdScalingRGCertificate.predictedExponent := by
  have hbridge :
      halfThirdScalingRGCertificate.RGToExponentBridge
        halfThirdScalingReparameterizedLength := by
    simpa using halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized
  simpa [halfThirdScalingRGCertificate] using
    certificate_hasCriticalNu_of_eventually_const_mul_le_le
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingModel
      hbridge
      halfThirdScalingReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      halfThirdScalingDoubledReparameterizedLength_comparable


end PackageReparameterizationComparisonExample
end Exact3D
end StatMech
