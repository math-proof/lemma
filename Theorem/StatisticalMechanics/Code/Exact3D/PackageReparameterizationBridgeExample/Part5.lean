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
import Def.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part5


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open PackageComparisonBridgeExample

open FiniteWitnessPackage

open FinitePlusTailHyperbolicSplitting


theorem
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      zeroStableKeyTableWitnessReparameterizedCorrelationLength β =
        zeroStableKeyTableWitnessCorrelationLength (toyLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl


theorem zeroStableKeyTableWitness_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_bridge
    zeroStableKeyTableWitnessBridge


theorem zeroStableKeyTableWitness_predictedExponent_eq :
    zeroStableKeyTableWitnessPackage.certificate.predictedExponent =
      predictedNu exampleScale 3 := by
  rw [InfiniteTailTableWitnessPackage.certificate_predictedExponent_eq]
  rfl


theorem zeroStableKeyTableWitness_hasCriticalNu_formulaTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessCorrelationLength
      (predictedNu exampleScale 3) := by
  simpa [zeroStableKeyTableWitness_predictedExponent_eq] using
    zeroStableKeyTableWitness_hasCriticalNu_target


theorem zeroStableKeyTableWitness_bridge_reparameterized_from_congrTarget :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      zeroStableKeyTableWitness_predictedExponent_eq
      zeroStableKeyTableWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_valid_reparameterized_from_congrTarget :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      zeroStableKeyTableWitness_predictedExponent_eq
      zeroStableKeyTableWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessReparameterizedCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  (zeroStableKeyTableWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      zeroStableKeyTableWitness_predictedExponent_eq
      zeroStableKeyTableWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq).hasCriticalNu


theorem zeroStableKeyTableWitness_bridge_reparameterized_from_targetExponent :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      zeroStableKeyTableWitness_hasCriticalNu_target
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_valid_reparameterized_from_targetExponent :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq
    zeroStableKeyTableWitness_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_targetExponent :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessReparameterizedCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    zeroStableKeyTableWitness_hasCriticalNu_target
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_bridge_reparameterized_from_externalBridge :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      zeroStableKeyTableWitnessPackage.certificate
      rfl
      zeroStableKeyTableWitnessBridge
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_valid_reparameterized_from_externalBridge :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_reparameterized_rgToExponentBridge_eventually_eq
    zeroStableKeyTableWitnessPackage.certificate
    rfl
    zeroStableKeyTableWitnessBridge
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem
    zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessReparameterizedCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    zeroStableKeyTableWitnessPackage.certificate
    rfl
    zeroStableKeyTableWitnessBridge
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitnessRetargetBridge :
    (zeroStableKeyTableWitnessPackage.certificate.retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        zeroStableKeyTableWitnessCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    zeroStableKeyTableWitnessCorrelationLength
    (zeroStableKeyTableWitnessPackage.certificate.retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using zeroStableKeyTableWitness_hasCriticalNu_target


theorem zeroStableKeyTableWitness_bridge_reparameterized_from_retargetBridge :
    zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      zeroStableKeyTableWitnessRetargetBridge
      toyLinearReparam_leftCritical
      zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_valid_reparameterized_from_retargetBridge :
    zeroStableKeyTableWitnessPackage.certificate.Valid
      zeroStableKeyTableWitnessReparameterizedCorrelationLength :=
  zeroStableKeyTableWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq
    zeroStableKeyTableWitnessRetargetBridge
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


theorem zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      zeroStableKeyTableWitnessReparameterizedCorrelationLength
      zeroStableKeyTableWitnessPackage.certificate.predictedExponent :=
  zeroStableKeyTableWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    zeroStableKeyTableWitnessRetargetBridge
    toyLinearReparam_leftCritical
    zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq


end PackageReparameterizationBridgeExample
end Exact3D
end StatMech
