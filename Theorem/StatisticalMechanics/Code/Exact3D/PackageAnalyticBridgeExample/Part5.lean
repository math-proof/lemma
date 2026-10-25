/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.WitnessAnalyticBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailAnalyticBridge
import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallAnalyticBridge
import Theorem.StatisticalMechanics.Code.Exact3D.PackagePowerLawBridgeExample
import Def.StatisticalMechanics.Code.Exact3D.PackageAnalyticBridgeExample.Part5


namespace StatMech

namespace Exact3D

namespace PackageAnalyticBridgeExample

open PackageComparisonBridgeExample

open PackagePowerLawBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open InfiniteTailTableClosedBallRGPackage


theorem zeroStableKeyTableWitness_bridge_from_analyticInputs :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs
    zeroStableKeyTableWitnessAnalyticBridgeInputs


theorem zeroStableKeyTableWitness_bridge_from_analyticInputs_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      rfl
      zeroStableKeyTableWitnessAnalyticBridgeInputs


theorem zeroStableKeyTableWitness_valid_from_analyticInputs_congr_pred :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.valid_of_analyticBridgeInputs_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      rfl
      zeroStableKeyTableWitnessAnalyticBridgeInputs


theorem zeroStableKeyTableWitness_hasCriticalNu_from_analyticInputs_congr_pred :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage
    |>.hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
      (D := zeroStableKeyTableWitnessPackage.certificate)
      rfl
      zeroStableKeyTableWitnessAnalyticBridgeInputs


theorem zeroStableKeyTableWitness_valid_from_analyticInputs :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_analyticBridgeInputs
    zeroStableKeyTableWitnessAnalyticBridgeInputs


theorem zeroStableKeyTableWitness_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_analyticBridgeInputs
    zeroStableKeyTableWitnessAnalyticBridgeInputs

section HyperbolicExamples

open FinitePlusTailHyperbolicSplitting


theorem halfThirdScalingHyperbolic_bridge_from_analyticInputs :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticBridgeInputs


theorem halfThirdScalingHyperbolic_valid_from_analyticInputs :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticBridgeInputs


theorem halfThirdScalingHyperbolic_hasCriticalNu_from_analyticInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_analyticBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticBridgeInputs


theorem halfThirdScalingHyperbolic_bridge_from_prefactorInputs :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem halfThirdScalingHyperbolic_valid_from_prefactorInputs :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticPrefactorBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem halfThirdScalingHyperbolic_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem halfThirdScalingHyperbolic_bridge_from_massInputs :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticMassBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticMassBridgeInputs


theorem halfThirdScalingHyperbolic_valid_from_massInputs :
    (halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticMassBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticMassBridgeInputs


theorem halfThirdScalingHyperbolic_hasCriticalNu_from_massInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingHyperbolicSplitting.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_analyticMassBridgeInputs
    halfThirdScalingHyperbolicSplitting
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingAnalyticMassBridgeInputs

end HyperbolicExamples


theorem halfThirdScalingBlockRGPackage_bridge_from_analyticInputs :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticBridgeInputs


theorem halfThirdScalingBlockRGPackage_bridge_from_prefactorInputs :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs


theorem halfThirdScalingBlockRGPackage_valid_from_analyticInputs :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  FinitePlusTailBlockRGPackage.certificate_valid_of_analyticBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticBridgeInputs


theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_analyticInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticBridgeInputs


theorem halfThirdScalingBlockRGPackage_valid_from_prefactorInputs :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  FinitePlusTailBlockRGPackage.certificate_valid_of_analyticPrefactorBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs


theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticPrefactorBridgeInputs


theorem halfThirdScalingBlockRGPackage_bridge_from_massInputs :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticMassBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticMassBridgeInputs


theorem halfThirdScalingBlockRGPackage_valid_from_massInputs :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  FinitePlusTailBlockRGPackage.certificate_valid_of_analyticMassBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticMassBridgeInputs


theorem halfThirdScalingBlockRGPackage_hasCriticalNu_from_massInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticMassBridgeInputs
    halfThirdScalingBlockRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingBlockRGAnalyticMassBridgeInputs

section ClosedBallExamples

open FinitePlusTailClosedBallRGPackage


theorem halfThirdScalingClosedBall_predictedExponent_eq_rg :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent =
      halfThirdScalingRGCertificate.predictedExponent := by
  rw [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq]


theorem halfThirdScalingClosedBall_bridge_from_analyticInputs :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem halfThirdScalingClosedBall_bridge_from_prefactorInputs :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem halfThirdScalingClosedBall_bridge_from_massInputs :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem halfThirdScalingClosedBall_valid_from_analyticInputs :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem halfThirdScalingClosedBall_hasCriticalNu_from_analyticInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem halfThirdScalingClosedBall_valid_from_prefactorInputs :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem halfThirdScalingClosedBall_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem halfThirdScalingClosedBall_valid_from_massInputs :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem halfThirdScalingClosedBall_hasCriticalNu_from_massInputs :
    HasCriticalNu halfThirdScalingModel
      halfThirdScalingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent :=
  certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    halfThirdScalingUnitClosedBallRGPackage
    halfThirdScalingBlockScale
    halfThirdScalingModel
    halfThirdScalingClosedBall_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs

end ClosedBallExamples


theorem zeroTableClosedBallRGPackage_bridge_from_analyticInputs :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem zeroTableClosedBallRGPackage_valid_from_analyticInputs :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem zeroTableClosedBallRGPackage_bridge_from_prefactorInputs :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem zeroTableClosedBallRGPackage_valid_from_prefactorInputs :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem zeroTableClosedBallRGPackage_bridge_from_massInputs :
    (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge
      halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem zeroTableClosedBallRGPackage_valid_from_massInputs :
    (zeroTableClosedBallRGPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem zeroTableClosedBallRGPackage_hasCriticalNu_from_massInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    zeroTableClosedBallRGPackage
    exampleScale
    zeroTableClosedBallRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem generatedReplacedTCBRGPackage_bridge_from_analyticInputs :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem generatedReplacedTCBRGPackage_valid_from_analyticInputs :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_bridge_from_analyticInputs :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_valid_from_analyticInputs :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_bridge_from_analyticInputs :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_valid_from_analyticInputs :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_bridge_from_analyticInputs :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_valid_from_analyticInputs :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticBridgeInputs


theorem generatedReplacedTCBRGPackage_bridge_from_prefactorInputs :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem generatedReplacedTCBRGPackage_valid_from_prefactorInputs :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_bridge_from_prefactorInputs :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_valid_from_prefactorInputs :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_bridge_from_prefactorInputs :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_valid_from_prefactorInputs :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_bridge_from_prefactorInputs :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_valid_from_prefactorInputs :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticPrefactorBridgeInputs


theorem generatedReplacedTCBRGPackage_bridge_from_massInputs :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem generatedReplacedTCBRGPackage_valid_from_massInputs :
    (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem generatedReplacedTCBRGPackage_hasCriticalNu_from_massInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (generatedStableKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    generatedStableKeyReplacedTableClosedBallRGPackage
    exampleScale
    generatedReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_bridge_from_massInputs :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_valid_from_massInputs :
    (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
      exampleScale).Valid halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate
        exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    genMinCubicKeyReplacedTableClosedBallRGPackage
    exampleScale
    genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_bridge_from_massInputs :
    (genBoundedCaseReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_valid_from_massInputs :
    (genBoundedCaseReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    genBoundedCaseReplacedPackage
    exampleScale
    genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_bridge_from_massInputs :
    (genCubicClassReplacedPackage.certificate
      exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength :=
  certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_valid_from_massInputs :
    (genCubicClassReplacedPackage.certificate exampleScale).Valid
      halfThirdScalingCorrelationLength :=
  certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs


theorem genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massInputs :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      halfThirdScalingCorrelationLength
      (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent :=
  certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent
    genCubicClassReplacedPackage
    exampleScale
    genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg
    halfThirdScalingAnalyticMassBridgeInputs

end PackageAnalyticBridgeExample
end Exact3D
end StatMech
