/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridge
import Def.StatisticalMechanics.Code.Exact3D.PackageReparameterizationComparisonExample.Part3


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationComparisonExample

open FinitePlusTailContractionExample

open FiniteWitnessPackageExample

open PackageReparameterizationBridgeExample

open FinitePlusTailHyperbolicSplitting

open InfiniteTailTableClosedBallRGPackage


theorem generatedReplacedReparameterizedLength_pos :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      0 < zeroTableClosedBallReparameterizedLength β :=
  Filter.Eventually.of_forall fun _ => by
    dsimp [zeroTableClosedBallReparameterizedLength,
      halfThirdScalingCorrelationLength]
    exact Real.exp_pos _


theorem generatedReplacedDoubledReparameterizedLength_comparable :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      (2 : ℝ) * zeroTableClosedBallReparameterizedLength β ≤
          generatedReplacedDoubledReparameterizedLength β ∧
        generatedReplacedDoubledReparameterizedLength β ≤
          (2 : ℝ) * zeroTableClosedBallReparameterizedLength β :=
  Filter.Eventually.of_forall fun β => by
    simp [generatedReplacedDoubledReparameterizedLength,
      halfThirdScalingDoublePrefactor]


theorem generatedReplacedTCBRGPackage_bridge_doubled_reparameterized :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      generatedReplacedDoubledReparameterizedLength := by
  have hbridge :
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using generatedReplacedTCBRGPackage_bridge_reparameterized
  exact
    generatedStableKeyReplacedTableClosedBallRGPackage
      |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
        exampleScale
        hbridge
        generatedReplacedReparameterizedLength_pos
        (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 2)
        generatedReplacedDoubledReparameterizedLength_comparable


theorem generatedReplacedTCBRGPackage_valid_doubled_reparameterized :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid generatedReplacedDoubledReparameterizedLength := by
  have hbridge :
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized
  exact
    certificate_valid_of_eventually_const_mul_le_le
      generatedStableKeyReplacedTableClosedBallRGPackage
      exampleScale
      hbridge
      generatedReplacedReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      generatedReplacedDoubledReparameterizedLength_comparable


theorem generatedReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      generatedReplacedDoubledReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  have hbridge :
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized
  exact
    certificate_hasCriticalNu_of_eventually_const_mul_le_le
      generatedStableKeyReplacedTableClosedBallRGPackage
      exampleScale
      hbridge
      generatedReplacedReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      generatedReplacedDoubledReparameterizedLength_comparable


theorem genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_reparameterized :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      generatedReplacedDoubledReparameterizedLength := by
  have hbridge :
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized
  exact
    genMinCubicKeyReplacedTableClosedBallRGPackage
      |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
        exampleScale
        hbridge
        generatedReplacedReparameterizedLength_pos
        (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 2)
        generatedReplacedDoubledReparameterizedLength_comparable


theorem genMinCubicKeyReplacedTCBRGPackage_valid_doubled_reparameterized :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid generatedReplacedDoubledReparameterizedLength := by
  have hbridge :
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized
  exact
    certificate_valid_of_eventually_const_mul_le_le
      genMinCubicKeyReplacedTableClosedBallRGPackage
      exampleScale
      hbridge
      generatedReplacedReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      generatedReplacedDoubledReparameterizedLength_comparable


theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      generatedReplacedDoubledReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  have hbridge :
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized
  exact
    certificate_hasCriticalNu_of_eventually_const_mul_le_le
      genMinCubicKeyReplacedTableClosedBallRGPackage
      exampleScale
      hbridge
      generatedReplacedReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      generatedReplacedDoubledReparameterizedLength_comparable


theorem genBoundedCaseReplacedTCBRGPackage_bridge_doubled_reparameterized :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      generatedReplacedDoubledReparameterizedLength := by
  have hbridge :
      (genBoundedCaseReplacedPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized
  exact
    genBoundedCaseReplacedPackage
      |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
        exampleScale
        hbridge
        generatedReplacedReparameterizedLength_pos
        (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 2)
        generatedReplacedDoubledReparameterizedLength_comparable


theorem genBoundedCaseReplacedTCBRGPackage_valid_doubled_reparameterized :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      generatedReplacedDoubledReparameterizedLength := by
  have hbridge :
      (genBoundedCaseReplacedPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized
  exact
    certificate_valid_of_eventually_const_mul_le_le
      genBoundedCaseReplacedPackage
      exampleScale
      hbridge
      generatedReplacedReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      generatedReplacedDoubledReparameterizedLength_comparable


theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      generatedReplacedDoubledReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  have hbridge :
      (genBoundedCaseReplacedPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized
  exact
    certificate_hasCriticalNu_of_eventually_const_mul_le_le
      genBoundedCaseReplacedPackage
      exampleScale
      hbridge
      generatedReplacedReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      generatedReplacedDoubledReparameterizedLength_comparable


theorem genCubicClassReplacedTCBRGPackage_bridge_doubled_reparameterized :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      generatedReplacedDoubledReparameterizedLength := by
  have hbridge :
      (genCubicClassReplacedPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genCubicClassReplacedTCBRGPackage_bridge_reparameterized
  exact
    genCubicClassReplacedPackage
      |>.certificate_rgToExponentBridge_of_eventually_const_mul_le_le
        exampleScale
        hbridge
        generatedReplacedReparameterizedLength_pos
        (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 2)
        generatedReplacedDoubledReparameterizedLength_comparable


theorem genCubicClassReplacedTCBRGPackage_valid_doubled_reparameterized :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      generatedReplacedDoubledReparameterizedLength := by
  have hbridge :
      (genCubicClassReplacedPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized
  exact
    certificate_valid_of_eventually_const_mul_le_le
      genCubicClassReplacedPackage
      exampleScale
      hbridge
      generatedReplacedReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      generatedReplacedDoubledReparameterizedLength_comparable


theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      generatedReplacedDoubledReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  have hbridge :
      (genCubicClassReplacedPackage.certificate
        exampleScale).RGToExponentBridge
        zeroTableClosedBallReparameterizedLength := by
    simpa using genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized
  exact
    certificate_hasCriticalNu_of_eventually_const_mul_le_le
      genCubicClassReplacedPackage
      exampleScale
      hbridge
      generatedReplacedReparameterizedLength_pos
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      generatedReplacedDoubledReparameterizedLength_comparable

end PackageReparameterizationComparisonExample
end Exact3D
end StatMech
