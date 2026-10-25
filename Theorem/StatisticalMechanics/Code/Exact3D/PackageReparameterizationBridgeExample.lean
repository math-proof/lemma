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
import Def.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample


namespace StatMech

namespace Exact3D

namespace PackageReparameterizationBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample

open PackageComparisonBridgeExample

open FiniteWitnessPackage

open FinitePlusTailHyperbolicSplitting


theorem hierarchicalLinearReparam_leftCritical :
    LeftCriticalReparam HierarchicalModel HierarchicalModel
      hierarchicalLinearReparam :=
  LeftCriticalReparam.linear HierarchicalModel HierarchicalModel
    (by norm_num : (0 : ℝ) < 2)


theorem hierarchicalReparameterizedLength_eventually_eq :
    ∀ᶠ β in nhdsWithin HierarchicalModel.betaC (Set.Iio HierarchicalModel.betaC),
      hierarchicalReparameterizedLength β =
        hierarchicalCorrelationLength (hierarchicalLinearReparam β) :=
  Filter.Eventually.of_forall fun _ => rfl


theorem hierarchicalWitness_hasCriticalNu_target :
    HasCriticalNu HierarchicalModel hierarchicalCorrelationLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
  simpa [hierarchicalContributionSplitWitnessPackage_predictedExponent_eq,
    hierarchicalNu, hierarchicalCertificate, predictedNu] using
    hierarchical_hasCriticalNu


theorem hierarchicalWitness_predictedExponent_eq_hierarchicalNu :
    hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent =
      hierarchicalNu := by
  rw [hierarchicalContributionSplitWitnessPackage_predictedExponent_eq]
  rfl


theorem
    hierarchicalWitness_bridge_reparameterized_from_namedTargetExponent_congr :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      hierarchicalWitness_predictedExponent_eq_hierarchicalNu
      hierarchical_hasCriticalNu
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq


theorem
    hierarchicalWitness_valid_reparameterized_from_namedTargetExponent_congr :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      hierarchicalWitness_predictedExponent_eq_hierarchicalNu
      hierarchical_hasCriticalNu
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq


theorem
    hierarchicalWitness_hasCriticalNu_reparameterized_from_namedTargetExponent_congr :
    HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hierarchicalContributionSplitWitnessPackage
    |>.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent
      hierarchicalWitness_predictedExponent_eq_hierarchicalNu
      hierarchical_hasCriticalNu
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalWitness_bridge_reparameterized_from_targetExponent :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq
      hierarchicalWitness_hasCriticalNu_target
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalWitness_valid_reparameterized_from_targetExponent :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq
    hierarchicalWitness_hasCriticalNu_target
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalWitness_hasCriticalNu_reparameterized_from_targetExponent :
    HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq
    hierarchicalContributionSplitWitnessPackage
    hierarchicalWitness_hasCriticalNu_target
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalCertificate_predicted_eq_witness :
    hierarchicalCertificate.predictedExponent =
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
  rw [hierarchicalContributionSplitWitnessPackage_predictedExponent_eq]
  rfl


theorem hierarchicalWitness_bridge_reparameterized_from_externalBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq
      hierarchicalCertificate
      hierarchicalCertificate_predicted_eq_witness
      hierarchical_bridge_via_exact_power
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalWitness_valid_reparameterized_from_externalBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      hierarchicalReparameterizedLength :=
  valid_of_reparameterized_rgToExponentBridge_eventually_eq
    hierarchicalContributionSplitWitnessPackage
    hierarchicalCertificate
    hierarchicalCertificate_predicted_eq_witness
    hierarchical_bridge_via_exact_power
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalWitness_hasCriticalNu_reparameterized_from_externalBridge :
    HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq
    hierarchicalContributionSplitWitnessPackage
    hierarchicalCertificate
    hierarchicalCertificate_predicted_eq_witness
    hierarchical_bridge_via_exact_power
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalWitnessRetargetBridge :
    (hierarchicalContributionSplitWitnessPackage.certificate.retarget
      HierarchicalModel).RGToExponentBridge hierarchicalCorrelationLength := by
  change HasCriticalNu HierarchicalModel hierarchicalCorrelationLength
    (hierarchicalContributionSplitWitnessPackage.certificate.retarget
      HierarchicalModel).predictedExponent
  simpa using hierarchicalWitness_hasCriticalNu_target


theorem hierarchicalWitness_bridge_reparameterized_from_retargetBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage
    |>.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq
      hierarchicalWitnessRetargetBridge
      hierarchicalLinearReparam_leftCritical
      hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalWitness_valid_reparameterized_from_retargetBridge :
    hierarchicalContributionSplitWitnessPackage.certificate.Valid
      hierarchicalReparameterizedLength :=
  hierarchicalContributionSplitWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq
    hierarchicalWitnessRetargetBridge
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq


theorem hierarchicalWitness_hasCriticalNu_reparameterized_from_retargetBridge :
    HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength
      hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent :=
  FiniteWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq
    hierarchicalContributionSplitWitnessPackage
    hierarchicalWitnessRetargetBridge
    hierarchicalLinearReparam_leftCritical
    hierarchicalReparameterizedLength_eventually_eq


end PackageReparameterizationBridgeExample
end Exact3D
end StatMech
