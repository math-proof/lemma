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
import Def.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part2


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open PackageComparisonBridgeExample

open FiniteWitnessPackage

open FinitePlusTailHyperbolicSplitting


theorem halfThirdScalingLinearReparam_leftCritical :
    LeftCriticalReparam halfThirdScalingModel halfThirdScalingModel
      halfThirdScalingLinearReparam :=
  LeftCriticalReparam.linear halfThirdScalingModel halfThirdScalingModel
    (by norm_num : (0 : ℝ) < 2)


theorem halfThirdScalingReparameterizedLength_eventually_eq :
    ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC
        (Set.Iio halfThirdScalingModel.betaC),
      halfThirdScalingReparameterizedLength β =
        halfThirdScalingCorrelationLength
          (halfThirdScalingLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl


theorem halfThirdScalingHyperbolicSplitting_bridge_reparameterized :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingHyperbolicSplitting_valid_reparameterized :
    halfThirdScalingRGCertificate.Valid
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      halfThirdScalingRGCertificate.predictedExponent := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_externalBridge :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate
      rfl
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_externalBridge :
    halfThirdScalingRGCertificate.Valid
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate
      rfl
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      halfThirdScalingRGCertificate.predictedExponent := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingRGCertificate
      rfl
      halfThirdScalingRGCertificate_bridge_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingHyperbolicSplittingRetargetBridge :
    ((halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength := by
  change HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
    ((halfThirdScalingHyperbolicSplitting.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).predictedExponent
  simpa [halfThirdScalingRGCertificate] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs


theorem
    halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_retargetBridge :
    halfThirdScalingRGCertificate.RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingHyperbolicSplittingRetargetBridge
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_retargetBridge :
    halfThirdScalingRGCertificate.Valid
      halfThirdScalingReparameterizedLength := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_valid_of_reparameterized_retargetBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingHyperbolicSplittingRetargetBridge
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      halfThirdScalingRGCertificate.predictedExponent := by
  simpa [halfThirdScalingRGCertificate] using
    certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
      halfThirdScalingHyperbolicSplitting
      halfThirdScalingBlockScale
      halfThirdScalingHyperbolicSplittingRetargetBridge
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_bridge_reparameterized_from_congrTarget :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    halfThirdScalingBlockScale
    (by
      rw [halfThirdScalingBlockRGPackage_predictedExponent_eq,
        halfThirdScalingRGCertificate_predictedExponent_eq])
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_valid_reparameterized_from_congrTarget :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    halfThirdScalingBlockScale
    (by
      rw [halfThirdScalingBlockRGPackage_predictedExponent_eq,
        halfThirdScalingRGCertificate_predictedExponent_eq])
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingBlockRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      halfThirdScalingBlockScale
      (by
        rw [halfThirdScalingBlockRGPackage_predictedExponent_eq,
          halfThirdScalingRGCertificate_predictedExponent_eq])
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq).hasCriticalNu


theorem halfThirdScalingBlockRGPackage_bridge_reparameterized :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_valid_reparameterized :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingBlockRGPackage_bridge_reparameterized_from_externalBridge :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate
    rfl
    halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_valid_reparameterized_from_externalBridge :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate
    rfl
    halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGCertificate
    rfl
    halfThirdScalingBlockRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackageRetargetBridge :
    ((halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength := by
  change HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
    ((halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).predictedExponent
  simpa [halfThirdScalingBlockRGCertificate] using
    halfThirdScalingBlockRGCertificate_hasCriticalNu_from_prefactorInputs


theorem halfThirdScalingBlockRGPackage_bridge_reparameterized_from_retargetBridge :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_valid_reparameterized_from_retargetBridge :
    (halfThirdScalingBlockRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingBlockRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingBlockRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingBlockRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target :
    HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  simpa [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
    halfThirdScalingRGCertificate_predictedExponent_eq] using
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs


theorem
    halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_congrTarget :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent
    halfThirdScalingBlockScale
    (by
      rw [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
        halfThirdScalingRGCertificate_predictedExponent_eq])
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_congrTarget :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
    halfThirdScalingBlockScale
    (by
      rw [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
        halfThirdScalingRGCertificate_predictedExponent_eq])
    halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact
    (P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      halfThirdScalingBlockScale
      (by
        rw [halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq,
          halfThirdScalingRGCertificate_predictedExponent_eq])
      halfThirdScalingRGCertificate_hasCriticalNu_from_prefactorInputs
      halfThirdScalingLinearReparam_leftCritical
      halfThirdScalingReparameterizedLength_eventually_eq).hasCriticalNu


theorem halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_externalBridge :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingRGCertificate
    (by
      rw [halfThirdScalingRGCertificate_predictedExponent_eq,
        halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq])
    halfThirdScalingRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_externalBridge :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingRGCertificate
    (by
      rw [halfThirdScalingRGCertificate_predictedExponent_eq,
        halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq])
    halfThirdScalingRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingRGCertificate
    (by
      rw [halfThirdScalingRGCertificate_predictedExponent_eq,
        halfThirdScalingUnitClosedBallRGPackage_predictedExponent_eq])
    halfThirdScalingRGCertificate_bridge_from_prefactorInputs
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem halfThirdScalingUnitClosedBallRGPackageRetargetBridge :
    ((halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingCorrelationLength := by
  change HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength
    ((halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).retarget
        halfThirdScalingModel).predictedExponent
  simpa using halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target


theorem
    halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_retargetBridge :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_retargetBridge :
    (halfThirdScalingUnitClosedBallRGPackage.certificate
      halfThirdScalingBlockScale halfThirdScalingModel).Valid
      halfThirdScalingReparameterizedLength := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_valid_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


theorem
    halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength
      (halfThirdScalingUnitClosedBallRGPackage.certificate
        halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
  let P := halfThirdScalingUnitClosedBallRGPackage
  exact P.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    halfThirdScalingBlockScale
    halfThirdScalingUnitClosedBallRGPackageRetargetBridge
    halfThirdScalingLinearReparam_leftCritical
    halfThirdScalingReparameterizedLength_eventually_eq


end PackageReparameterizationBridgeExample
end Exact3D
end StatMech
