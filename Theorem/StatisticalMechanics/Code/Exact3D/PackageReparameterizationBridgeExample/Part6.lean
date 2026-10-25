/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.WitnessReparameterizationBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailReparameterizationBridge
import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallReparameterizationBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part58
import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridgeExample.Part7
import Def.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part6


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open PackageComparisonBridgeExample

open FiniteWitnessPackage

open FinitePlusTailHyperbolicSplitting


theorem zeroTableClosedBallReparameterizedLength_eventually_eq :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      zeroTableClosedBallReparameterizedLength β =
        halfThirdScalingCorrelationLength (toyLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl


theorem zeroTableClosedBallRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  simpa [zeroTableClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs


theorem zeroTableClosedBallRGPackage_bridge_reparameterized_from_congrTarget :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq] using
        zeroTableClosedBallRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem zeroTableClosedBallRGPackage_valid_reparameterized_from_congrTarget :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [zeroTableClosedBallRGPackage_predictedExponent_eq] using
        zeroTableClosedBallRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
  let P := zeroTableClosedBallRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      zeroTableClosedBallRGPackage_predictedExponent_eq
      (by
        simpa [zeroTableClosedBallRGPackage_predictedExponent_eq] using
          zeroTableClosedBallRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu


theorem zeroTableClosedBallRGPackage_bridge_reparameterized :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem zeroTableClosedBallRGPackage_valid_reparameterized :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem zeroTableClosedBallRGPackageBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent
  exact zeroTableClosedBallRGPackage_hasCriticalNu_target


theorem zeroTableClosedBallRGPackage_bridge_reparameterized_from_externalBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    zeroTableClosedBallRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem zeroTableClosedBallRGPackage_valid_reparameterized_from_externalBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    zeroTableClosedBallRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    zeroTableClosedBallRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem zeroTableClosedBallRGPackageRetargetBridge :
    ((zeroTableClosedBallRGPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((zeroTableClosedBallRGPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using zeroTableClosedBallRGPackage_hasCriticalNu_target


theorem zeroTableClosedBallRGPackage_bridge_reparameterized_from_retargetBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem zeroTableClosedBallRGPackage_valid_reparameterized_from_retargetBridge :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
  let P := zeroTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    zeroTableClosedBallRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  simpa [
    generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs


theorem generatedReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [
        generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        using generatedReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackage_valid_reparameterized_from_congrTarget :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [
        generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        using generatedReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
      (by
        simpa [
          generatedStableKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
          using generatedReplacedTCBRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu


theorem generatedReplacedTCBRGPackage_bridge_reparameterized :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackage_valid_reparameterized :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackageBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).predictedExponent
  exact generatedReplacedTCBRGPackage_hasCriticalNu_target


theorem generatedReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    generatedReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackage_valid_reparameterized_from_externalBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    generatedReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    generatedReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackageRetargetBridge :
    ((generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).retarget
        (ToyCriticalModel exampleScale 3)).RGToExponentBridge
          halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).retarget
        (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using generatedReplacedTCBRGPackage_hasCriticalNu_target


theorem generatedReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem generatedReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := generatedStableKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    generatedReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  simpa [
    genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs


theorem genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [
        genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_congrTarget :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
    (by
      simpa [
        genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
        using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq
      (by
        simpa [
          genMinCubicKeyReplacedTableClosedBallRGPackage_predictedExponent_eq]
          using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu


theorem genMinCubicKeyReplacedTCBRGPackageBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).predictedExponent
  exact genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target


theorem
    genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genMinCubicKeyReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_externalBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genMinCubicKeyReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genMinCubicKeyReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genMinCubicKeyReplacedTCBRGPackageRetargetBridge :
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).retarget
        (ToyCriticalModel exampleScale 3)).RGToExponentBridge
          halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).retarget
        (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target


theorem
    genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent := by
  let P := genMinCubicKeyReplacedTableClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genMinCubicKeyReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  simpa [
    genBoundedCaseReplacedPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs


theorem genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genBoundedCaseReplacedTCBRGPackage_valid_reparameterized :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    genBoundedCaseReplacedPackage_predictedExponent_eq
    (by
      simpa [genBoundedCaseReplacedPackage_predictedExponent_eq]
        using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_congrTarget :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    genBoundedCaseReplacedPackage_predictedExponent_eq
    (by
      simpa [genBoundedCaseReplacedPackage_predictedExponent_eq]
        using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genBoundedCaseReplacedPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      genBoundedCaseReplacedPackage_predictedExponent_eq
      (by
        simpa [genBoundedCaseReplacedPackage_predictedExponent_eq]
          using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu


theorem genBoundedCaseReplacedTCBRGPackageBridge :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent
  exact genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target


theorem
    genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genBoundedCaseReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_externalBridge :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genBoundedCaseReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genBoundedCaseReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genBoundedCaseReplacedTCBRGPackageRetargetBridge :
    ((genBoundedCaseReplacedPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((genBoundedCaseReplacedPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target


theorem
    genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge :
    (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genBoundedCaseReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genBoundedCaseReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  simpa [
    genCubicClassReplacedPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs


theorem genCubicClassReplacedTCBRGPackage_bridge_reparameterized :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genCubicClassReplacedTCBRGPackage_valid_reparameterized :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    exampleScale
    genCubicClassReplacedPackage_predictedExponent_eq
    (by
      simpa [genCubicClassReplacedPackage_predictedExponent_eq]
        using genCubicClassReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_congrTarget :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    exampleScale
    genCubicClassReplacedPackage_predictedExponent_eq
    (by
      simpa [genCubicClassReplacedPackage_predictedExponent_eq]
        using genCubicClassReplacedTCBRGPackage_hasCriticalNu_target)
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genCubicClassReplacedPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      exampleScale
      genCubicClassReplacedPackage_predictedExponent_eq
      (by
        simpa [genCubicClassReplacedPackage_predictedExponent_eq]
          using genCubicClassReplacedTCBRGPackage_hasCriticalNu_target)
      toyLinearReparam_leftCritical
      zeroTableClosedBallReparameterizedLength_eventually_eq).hasCriticalNu


theorem genCubicClassReplacedTCBRGPackageBridge :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent
  exact genCubicClassReplacedTCBRGPackage_hasCriticalNu_target


theorem
    genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genCubicClassReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_externalBridge :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genCubicClassReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    exampleScale
    (P.certificate exampleScale)
    rfl
    genCubicClassReplacedTCBRGPackageBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem genCubicClassReplacedTCBRGPackageRetargetBridge :
    ((genCubicClassReplacedPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        halfThirdScalingCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    halfThirdScalingCorrelationLength
    ((genCubicClassReplacedPackage.certificate exampleScale).retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using genCubicClassReplacedTCBRGPackage_hasCriticalNu_target


theorem
    genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge :
    (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      zeroTableClosedBallReparameterizedLength := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq


theorem
    genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroTableClosedBallReparameterizedLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
  let P := genCubicClassReplacedPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    exampleScale
    genCubicClassReplacedTCBRGPackageRetargetBridge
    toyLinearReparam_leftCritical
    zeroTableClosedBallReparameterizedLength_eventually_eq

end PackageReparameterizationBridgeExample
end Exact3D
end StatMech
