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
import Def.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample.Part4


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open PackageComparisonBridgeExample

open FiniteWitnessPackage

open FinitePlusTailHyperbolicSplitting


theorem geometricTailReparameterizedCorrelationLength_eventually_eq :
    ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC
        (Set.Iio (ToyCriticalModel exampleScale 3).betaC),
      geometricTailReparameterizedCorrelationLength β =
        geometricTailCorrelationLength (toyLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl


theorem geometricTailWitness_hasCriticalNu_target :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_bridge
    geometricTailWitnessBridge


theorem geometricTailWitness_predictedExponent_eq :
    geometricTailWitnessPackage.certificate.predictedExponent =
      predictedNu exampleScale 3 := by
  rw [InfiniteTailWitnessPackage.certificate_predictedExponent_eq]
  rfl


theorem geometricTailWitness_hasCriticalNu_formulaTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailCorrelationLength (predictedNu exampleScale 3) := by
  simpa [geometricTailWitness_predictedExponent_eq] using
    geometricTailWitness_hasCriticalNu_target


theorem geometricTailWitness_bridge_reparameterized_from_congrTarget :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      geometricTailWitness_predictedExponent_eq
      geometricTailWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_valid_reparameterized_from_congrTarget :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      geometricTailWitness_predictedExponent_eq
      geometricTailWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_hasCriticalNu_reparameterized_from_congrTarget :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailReparameterizedCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  (geometricTailWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      geometricTailWitness_predictedExponent_eq
      geometricTailWitness_hasCriticalNu_formulaTarget
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq).hasCriticalNu


theorem geometricTailWitness_bridge_reparameterized_from_targetExponent :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      geometricTailWitness_hasCriticalNu_target
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_valid_reparameterized_from_targetExponent :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq
    geometricTailWitness_hasCriticalNu_target
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_hasCriticalNu_reparameterized_from_targetExponent :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailReparameterizedCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    geometricTailWitness_hasCriticalNu_target
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_bridge_reparameterized_from_externalBridge :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      geometricTailWitnessPackage.certificate
      rfl
      geometricTailWitnessBridge
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_valid_reparameterized_from_externalBridge :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage.valid_of_reparameterized_rgToExponentBridge_eventually_eq
    geometricTailWitnessPackage.certificate
    rfl
    geometricTailWitnessBridge
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailReparameterizedCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    geometricTailWitnessPackage.certificate
    rfl
    geometricTailWitnessBridge
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitnessRetargetBridge :
    (geometricTailWitnessPackage.certificate.retarget
      (ToyCriticalModel exampleScale 3)).RGToExponentBridge
        geometricTailCorrelationLength := by
  change HasCriticalNu (ToyCriticalModel exampleScale 3)
    geometricTailCorrelationLength
    (geometricTailWitnessPackage.certificate.retarget
      (ToyCriticalModel exampleScale 3)).predictedExponent
  simpa using geometricTailWitness_hasCriticalNu_target


theorem geometricTailWitness_bridge_reparameterized_from_retargetBridge :
    geometricTailWitnessPackage.certificate.RGToExponentBridge
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      geometricTailWitnessRetargetBridge
      toyLinearReparam_leftCritical
      geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_valid_reparameterized_from_retargetBridge :
    geometricTailWitnessPackage.certificate.Valid
      geometricTailReparameterizedCorrelationLength :=
  geometricTailWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq
    geometricTailWitnessRetargetBridge
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq


theorem geometricTailWitness_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu (ToyCriticalModel exampleScale 3)
      geometricTailReparameterizedCorrelationLength
      geometricTailWitnessPackage.certificate.predictedExponent :=
  geometricTailWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    geometricTailWitnessRetargetBridge
    toyLinearReparam_leftCritical
    geometricTailReparameterizedCorrelationLength_eventually_eq


end PackageReparameterizationBridgeExample
end Exact3D
end StatMech
