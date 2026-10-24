import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.PackageReparameterizationBridgeExample
open StatMech StatMech.Exact3D StatMech.Exact3D.PackageReparameterizationBridgeExample


/--
[hierarchicalLinearReparam_leftCritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalLinearReparam_leftCritical_eq :
-- imply
  LeftCriticalReparam HierarchicalModel HierarchicalModel hierarchicalLinearReparam := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalLinearReparam_leftCritical

/--
[hierarchicalReparameterizedLength_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalReparameterizedLength_eventually_eq_eq :
-- imply
  ∀ᶠ β in nhdsWithin HierarchicalModel.betaC (Set.Iio HierarchicalModel.betaC), hierarchicalReparameterizedLength β = hierarchicalCorrelationLength (hierarchicalLinearReparam β) := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalReparameterizedLength_eventually_eq

/--
[hierarchicalWitness_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu HierarchicalModel hierarchicalCorrelationLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_hasCriticalNu_target

/--
[hierarchicalWitness_predictedExponent_eq_hierarchicalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_predictedExponent_eq_hierarchicalNu_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent = hierarchicalNu := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_predictedExponent_eq_hierarchicalNu

/--
[hierarchicalWitness_bridge_reparameterized_from_namedTargetExponent_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_bridge_reparameterized_from_namedTargetExponent_congr_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge hierarchicalReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_bridge_reparameterized_from_namedTargetExponent_congr

/--
[hierarchicalWitness_valid_reparameterized_from_namedTargetExponent_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_valid_reparameterized_from_namedTargetExponent_congr_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.Valid hierarchicalReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_valid_reparameterized_from_namedTargetExponent_congr

/--
[hierarchicalWitness_hasCriticalNu_reparameterized_from_namedTargetExponent_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_hasCriticalNu_reparameterized_from_namedTargetExponent_congr_eq :
-- imply
  HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_hasCriticalNu_reparameterized_from_namedTargetExponent_congr

/--
[hierarchicalWitness_bridge_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_bridge_reparameterized_from_targetExponent_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge hierarchicalReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_bridge_reparameterized_from_targetExponent

/--
[hierarchicalWitness_valid_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_valid_reparameterized_from_targetExponent_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.Valid hierarchicalReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_valid_reparameterized_from_targetExponent

/--
[hierarchicalWitness_hasCriticalNu_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_hasCriticalNu_reparameterized_from_targetExponent_eq :
-- imply
  HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_hasCriticalNu_reparameterized_from_targetExponent

/--
[hierarchicalCertificate_predicted_eq_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalCertificate_predicted_eq_witness_eq :
-- imply
  hierarchicalCertificate.predictedExponent = hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalCertificate_predicted_eq_witness

/--
[hierarchicalWitness_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_bridge_reparameterized_from_externalBridge_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge hierarchicalReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_bridge_reparameterized_from_externalBridge

/--
[hierarchicalWitness_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_valid_reparameterized_from_externalBridge_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.Valid hierarchicalReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_valid_reparameterized_from_externalBridge

/--
[hierarchicalWitness_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_hasCriticalNu_reparameterized_from_externalBridge

/--
[hierarchicalWitnessRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitnessRetargetBridge_eq :
-- imply
  (hierarchicalContributionSplitWitnessPackage.certificate.retarget HierarchicalModel).RGToExponentBridge hierarchicalCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitnessRetargetBridge

/--
[hierarchicalWitness_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge hierarchicalReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_bridge_reparameterized_from_retargetBridge

/--
[hierarchicalWitness_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_valid_reparameterized_from_retargetBridge_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.Valid hierarchicalReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_valid_reparameterized_from_retargetBridge

/--
[hierarchicalWitness_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu HierarchicalModel hierarchicalReparameterizedLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.hierarchicalWitness_hasCriticalNu_reparameterized_from_retargetBridge

/--
[halfThirdScalingLinearReparam_leftCritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingLinearReparam_leftCritical_eq :
-- imply
  LeftCriticalReparam halfThirdScalingModel halfThirdScalingModel halfThirdScalingLinearReparam := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingLinearReparam_leftCritical

/--
[halfThirdScalingReparameterizedLength_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingReparameterizedLength_eventually_eq_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), halfThirdScalingReparameterizedLength β = halfThirdScalingCorrelationLength (halfThirdScalingLinearReparam β) := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingReparameterizedLength_eventually_eq

/--
[halfThirdScalingHyperbolicSplitting_bridge_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_bridge_reparameterized_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_bridge_reparameterized

/--
[halfThirdScalingHyperbolicSplitting_valid_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_valid_reparameterized_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_valid_reparameterized

/--
[halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized

/--
[halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_externalBridge_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_externalBridge

/--
[halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_externalBridge_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_externalBridge

/--
[halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_externalBridge

/--
[halfThirdScalingHyperbolicSplittingRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplittingRetargetBridge_eq :
-- imply
  ((halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).retarget halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplittingRetargetBridge

/--
[halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_bridge_reparameterized_from_retargetBridge

/--
[halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_retargetBridge_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_valid_reparameterized_from_retargetBridge

/--
[halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingHyperbolicSplitting_hasCriticalNu_reparameterized_from_retargetBridge

/--
[halfThirdScalingBlockRGPackage_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_reparameterized_from_congrTarget_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_bridge_reparameterized_from_congrTarget

/--
[halfThirdScalingBlockRGPackage_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_reparameterized_from_congrTarget_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_valid_reparameterized_from_congrTarget

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_congrTarget

/--
[halfThirdScalingBlockRGPackage_bridge_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_reparameterized_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_bridge_reparameterized

/--
[halfThirdScalingBlockRGPackage_valid_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_reparameterized_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_valid_reparameterized

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized

/--
[halfThirdScalingBlockRGPackage_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_reparameterized_from_externalBridge_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_bridge_reparameterized_from_externalBridge

/--
[halfThirdScalingBlockRGPackage_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_reparameterized_from_externalBridge_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_valid_reparameterized_from_externalBridge

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_externalBridge

/--
[halfThirdScalingBlockRGPackageRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackageRetargetBridge_eq :
-- imply
  ((halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).retarget halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackageRetargetBridge

/--
[halfThirdScalingBlockRGPackage_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_bridge_reparameterized_from_retargetBridge

/--
[halfThirdScalingBlockRGPackage_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_reparameterized_from_retargetBridge_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_valid_reparameterized_from_retargetBridge

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_reparameterized_from_retargetBridge

/--
[halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_target

/--
[halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_congrTarget_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_congrTarget

/--
[halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_congrTarget_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_congrTarget

/--
[halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget

/--
[halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized

/--
[halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized

/--
[halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized

/--
[halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_externalBridge_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_externalBridge

/--
[halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_externalBridge_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_externalBridge

/--
[halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge

/--
[halfThirdScalingUnitClosedBallRGPackageRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackageRetargetBridge_eq :
-- imply
  ((halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).retarget halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackageRetargetBridge

/--
[halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_bridge_reparameterized_from_retargetBridge

/--
[halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_retargetBridge_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_valid_reparameterized_from_retargetBridge

/--
[halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingReparameterizedLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge

/--
[toyLinearReparam_leftCritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma toyLinearReparam_leftCritical_eq :
-- imply
  LeftCriticalReparam (ToyCriticalModel exampleScale 3) (ToyCriticalModel exampleScale 3) toyLinearReparam := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.toyLinearReparam_leftCritical

/--
[geometricTailReparameterizedCorrelationLength_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailReparameterizedCorrelationLength_eventually_eq_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), geometricTailReparameterizedCorrelationLength β = geometricTailCorrelationLength (toyLinearReparam β) := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailReparameterizedCorrelationLength_eventually_eq

/--
[geometricTailWitness_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_hasCriticalNu_target

/--
[geometricTailWitness_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_predictedExponent_eq_eq :
-- imply
  geometricTailWitnessPackage.certificate.predictedExponent = predictedNu exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_predictedExponent_eq

/--
[geometricTailWitness_hasCriticalNu_formulaTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_formulaTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength (predictedNu exampleScale 3) := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_hasCriticalNu_formulaTarget

/--
[geometricTailWitness_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_reparameterized_from_congrTarget_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_bridge_reparameterized_from_congrTarget

/--
[geometricTailWitness_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_reparameterized_from_congrTarget_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_valid_reparameterized_from_congrTarget

/--
[geometricTailWitness_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailReparameterizedCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_hasCriticalNu_reparameterized_from_congrTarget

/--
[geometricTailWitness_bridge_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_reparameterized_from_targetExponent_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_bridge_reparameterized_from_targetExponent

/--
[geometricTailWitness_valid_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_reparameterized_from_targetExponent_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_valid_reparameterized_from_targetExponent

/--
[geometricTailWitness_hasCriticalNu_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_reparameterized_from_targetExponent_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailReparameterizedCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_hasCriticalNu_reparameterized_from_targetExponent

/--
[geometricTailWitness_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_reparameterized_from_externalBridge_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_bridge_reparameterized_from_externalBridge

/--
[geometricTailWitness_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_reparameterized_from_externalBridge_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_valid_reparameterized_from_externalBridge

/--
[geometricTailWitness_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailReparameterizedCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_hasCriticalNu_reparameterized_from_externalBridge

/--
[geometricTailWitnessRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessRetargetBridge_eq :
-- imply
  (geometricTailWitnessPackage.certificate.retarget (ToyCriticalModel exampleScale 3)).RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitnessRetargetBridge

/--
[geometricTailWitness_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_bridge_reparameterized_from_retargetBridge

/--
[geometricTailWitness_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_reparameterized_from_retargetBridge_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_valid_reparameterized_from_retargetBridge

/--
[geometricTailWitness_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailReparameterizedCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.geometricTailWitness_hasCriticalNu_reparameterized_from_retargetBridge

/--
[zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), zeroStableKeyTableWitnessReparameterizedCorrelationLength β = zeroStableKeyTableWitnessCorrelationLength (toyLinearReparam β) := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitnessReparameterizedCorrelationLength_eventually_eq

/--
[zeroStableKeyTableWitness_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_target

/--
[zeroStableKeyTableWitness_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_predictedExponent_eq_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.predictedExponent = predictedNu exampleScale 3 := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_predictedExponent_eq

/--
[zeroStableKeyTableWitness_hasCriticalNu_formulaTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_formulaTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength (predictedNu exampleScale 3) := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_formulaTarget

/--
[zeroStableKeyTableWitness_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_reparameterized_from_congrTarget_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_bridge_reparameterized_from_congrTarget

/--
[zeroStableKeyTableWitness_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_reparameterized_from_congrTarget_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_valid_reparameterized_from_congrTarget

/--
[zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessReparameterizedCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_congrTarget

/--
[zeroStableKeyTableWitness_bridge_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_reparameterized_from_targetExponent_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_bridge_reparameterized_from_targetExponent

/--
[zeroStableKeyTableWitness_valid_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_reparameterized_from_targetExponent_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_valid_reparameterized_from_targetExponent

/--
[zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_targetExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_targetExponent_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessReparameterizedCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_targetExponent

/--
[zeroStableKeyTableWitness_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_reparameterized_from_externalBridge_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_bridge_reparameterized_from_externalBridge

/--
[zeroStableKeyTableWitness_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_reparameterized_from_externalBridge_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_valid_reparameterized_from_externalBridge

/--
[zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessReparameterizedCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_externalBridge

/--
[zeroStableKeyTableWitnessRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessRetargetBridge_eq :
-- imply
  (zeroStableKeyTableWitnessPackage.certificate.retarget (ToyCriticalModel exampleScale 3)).RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitnessRetargetBridge

/--
[zeroStableKeyTableWitness_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_bridge_reparameterized_from_retargetBridge

/--
[zeroStableKeyTableWitness_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_reparameterized_from_retargetBridge_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessReparameterizedCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_valid_reparameterized_from_retargetBridge

/--
[zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessReparameterizedCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_reparameterized_from_retargetBridge

/--
[zeroTableClosedBallReparameterizedLength_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallReparameterizedLength_eventually_eq_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), zeroTableClosedBallReparameterizedLength β = halfThirdScalingCorrelationLength (toyLinearReparam β) := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallReparameterizedLength_eventually_eq

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_target

/--
[zeroTableClosedBallRGPackage_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_reparameterized_from_congrTarget_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_bridge_reparameterized_from_congrTarget

/--
[zeroTableClosedBallRGPackage_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_reparameterized_from_congrTarget_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_valid_reparameterized_from_congrTarget

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_congrTarget

/--
[zeroTableClosedBallRGPackage_bridge_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_reparameterized_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_bridge_reparameterized

/--
[zeroTableClosedBallRGPackage_valid_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_reparameterized_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_valid_reparameterized

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized

/--
[zeroTableClosedBallRGPackageBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackageBridge_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackageBridge

/--
[zeroTableClosedBallRGPackage_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_reparameterized_from_externalBridge_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_bridge_reparameterized_from_externalBridge

/--
[zeroTableClosedBallRGPackage_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_reparameterized_from_externalBridge_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_valid_reparameterized_from_externalBridge

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_externalBridge

/--
[zeroTableClosedBallRGPackageRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackageRetargetBridge_eq :
-- imply
  ((zeroTableClosedBallRGPackage.certificate exampleScale).retarget (ToyCriticalModel exampleScale 3)).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackageRetargetBridge

/--
[zeroTableClosedBallRGPackage_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_bridge_reparameterized_from_retargetBridge

/--
[zeroTableClosedBallRGPackage_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_reparameterized_from_retargetBridge_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_valid_reparameterized_from_retargetBridge

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_reparameterized_from_retargetBridge

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_target

/--
[generatedReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget

/--
[generatedReplacedTCBRGPackage_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_reparameterized_from_congrTarget_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_valid_reparameterized_from_congrTarget

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget

/--
[generatedReplacedTCBRGPackage_bridge_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_reparameterized_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_bridge_reparameterized

/--
[generatedReplacedTCBRGPackage_valid_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_reparameterized_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_valid_reparameterized

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized

/--
[generatedReplacedTCBRGPackageBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackageBridge_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackageBridge

/--
[generatedReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge

/--
[generatedReplacedTCBRGPackage_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_reparameterized_from_externalBridge_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_valid_reparameterized_from_externalBridge

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge

/--
[generatedReplacedTCBRGPackageRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackageRetargetBridge_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).retarget (ToyCriticalModel exampleScale 3)).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackageRetargetBridge

/--
[generatedReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge

/--
[generatedReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_target

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_congrTarget_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_congrTarget

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget

/--
[genMinCubicKeyReplacedTCBRGPackageBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackageBridge_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackageBridge

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_externalBridge_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_externalBridge

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge

/--
[genMinCubicKeyReplacedTCBRGPackageRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackageRetargetBridge_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).retarget (ToyCriticalModel exampleScale 3)).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackageRetargetBridge

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_target

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized

/--
[genBoundedCaseReplacedTCBRGPackage_valid_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_reparameterized

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget

/--
[genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_congrTarget_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_congrTarget

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget

/--
[genBoundedCaseReplacedTCBRGPackageBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackageBridge_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackageBridge

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge

/--
[genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_externalBridge_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_externalBridge

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge

/--
[genBoundedCaseReplacedTCBRGPackageRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackageRetargetBridge_eq :
-- imply
  ((genBoundedCaseReplacedPackage.certificate exampleScale).retarget (ToyCriticalModel exampleScale 3)).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackageRetargetBridge

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge

/--
[genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_target_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_target

/--
[genCubicClassReplacedTCBRGPackage_bridge_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_reparameterized_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_reparameterized

/--
[genCubicClassReplacedTCBRGPackage_valid_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_reparameterized_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_valid_reparameterized

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized

/--
[genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_congrTarget

/--
[genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_congrTarget_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_congrTarget

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_congrTarget

/--
[genCubicClassReplacedTCBRGPackageBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackageBridge_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackageBridge

/--
[genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_externalBridge

/--
[genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_externalBridge_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_externalBridge

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_externalBridge

/--
[genCubicClassReplacedTCBRGPackageRetargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackageRetargetBridge_eq :
-- imply
  ((genCubicClassReplacedPackage.certificate exampleScale).retarget (ToyCriticalModel exampleScale 3)).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackageRetargetBridge

/--
[genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_reparameterized_from_retargetBridge

/--
[genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid zeroTableClosedBallReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_valid_reparameterized_from_retargetBridge

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallReparameterizedLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_reparameterized_from_retargetBridge


-- created on 2026-10-23
