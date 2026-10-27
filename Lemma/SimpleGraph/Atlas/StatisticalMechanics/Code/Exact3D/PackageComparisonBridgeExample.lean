import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridgeExample.Part7
open StatMech StatMech.Exact3D StatMech.Exact3D.PackageComparisonBridgeExample


/--
[hierarchicalCorrelationLength_eventually_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma hierarchicalCorrelationLength_eventually_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin HierarchicalModel.betaC (Set.Iio HierarchicalModel.betaC), 0 < hierarchicalCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.hierarchicalCorrelationLength_eventually_pos

/--
[doubledHierarchicalCorrelationLength_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma doubledHierarchicalCorrelationLength_comparable_eq :
-- imply
  ∀ᶠ β in nhdsWithin HierarchicalModel.betaC (Set.Iio HierarchicalModel.betaC), (2 : ℝ) * hierarchicalCorrelationLength β ≤ doubledHierarchicalCorrelationLength β ∧ doubledHierarchicalCorrelationLength β ≤ (2 : ℝ) * hierarchicalCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.doubledHierarchicalCorrelationLength_comparable

/--
[hierarchicalWitnessBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitnessBridge_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge hierarchicalCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.hierarchicalWitnessBridge

/--
[hierarchicalWitnessBridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitnessBridge_doubled_by_package_comparison_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge doubledHierarchicalCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.hierarchicalWitnessBridge_doubled_by_package_comparison

/--
[hierarchicalWitness_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_valid_doubled_by_package_comparison_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.Valid doubledHierarchicalCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.hierarchicalWitness_valid_doubled_by_package_comparison

/--
[hierarchicalWitness_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma hierarchicalWitness_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu HierarchicalModel doubledHierarchicalCorrelationLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.hierarchicalWitness_hasCriticalNu_doubled_by_package_comparison

/--
[halfThirdScalingHyperbolicSplitting_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_bridge_doubled_by_package_comparison_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingHyperbolicSplitting_bridge_doubled_by_package_comparison

/--
[halfThirdScalingHyperbolicSplitting_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_valid_doubled_by_package_comparison_eq :
-- imply
  halfThirdScalingRGCertificate.Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingHyperbolicSplitting_valid_doubled_by_package_comparison

/--
[halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu halfThirdScalingModel (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_by_package_comparison

/--
[halfThirdScalingHyperbolicSplitting_bridge_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_bridge_doubled_by_package_prefactor_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingHyperbolicSplitting_bridge_doubled_by_package_prefactor

/--
[halfThirdScalingHyperbolicSplitting_valid_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_valid_doubled_by_package_prefactor_eq :
-- imply
  halfThirdScalingRGCertificate.Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingHyperbolicSplitting_valid_doubled_by_package_prefactor

/--
[halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_by_package_prefactor_eq :
-- imply
  HasCriticalNu halfThirdScalingModel (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_by_package_prefactor

/--
[halfThirdScalingBlockRGPackage_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_doubled_by_package_comparison_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingBlockRGPackage_bridge_doubled_by_package_comparison

/--
[halfThirdScalingBlockRGPackage_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_doubled_by_package_comparison_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingBlockRGPackage_valid_doubled_by_package_comparison

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu halfThirdScalingModel (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_doubled_by_package_comparison

/--
[halfThirdScalingUnitClosedBallRGPackage_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_bridge_doubled_by_package_comparison_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingUnitClosedBallRGPackage_bridge_doubled_by_package_comparison

/--
[halfThirdScalingUnitClosedBallRGPackage_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_valid_doubled_by_package_comparison_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingUnitClosedBallRGPackage_valid_doubled_by_package_comparison

/--
[halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu halfThirdScalingModel (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.halfThirdScalingUnitClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison

/--
[zeroTableClosedBallRGPackage_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_doubled_by_package_comparison_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_bridge_doubled_by_package_comparison

/--
[zeroTableClosedBallRGPackage_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_doubled_by_package_comparison_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_valid_doubled_by_package_comparison

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison

/--
[zeroTableClosedBallRGPackage_bridge_doubled_by_package_comparison_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_doubled_by_package_comparison_congr_predictedExponent_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_bridge_doubled_by_package_comparison_congr_predictedExponent

/--
[zeroTableClosedBallRGPackage_valid_doubled_by_package_comparison_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_doubled_by_package_comparison_congr_predictedExponent_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_valid_doubled_by_package_comparison_congr_predictedExponent

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_comparison_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_doubled_by_package_prefactor_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_bridge_doubled_by_package_prefactor

/--
[zeroTableClosedBallRGPackage_valid_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_doubled_by_package_prefactor_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_valid_doubled_by_package_prefactor

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_prefactor_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_doubled_by_package_prefactor

/--
[generatedReplacedTCBRGPackage_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_doubled_by_package_comparison_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.generatedReplacedTCBRGPackage_bridge_doubled_by_package_comparison

/--
[generatedReplacedTCBRGPackage_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_doubled_by_package_comparison_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.generatedReplacedTCBRGPackage_valid_doubled_by_package_comparison

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison

/--
[genStableReplacedTCB_bridge_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genStableReplacedTCB_bridge_doubled_by_comparison_congr_pred_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genStableReplacedTCB_bridge_doubled_by_comparison_congr_pred

/--
[genStableReplacedTCB_valid_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genStableReplacedTCB_valid_doubled_by_comparison_congr_pred_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genStableReplacedTCB_valid_doubled_by_comparison_congr_pred

/--
[genStableReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genStableReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genStableReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_doubled_by_package_prefactor_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.generatedReplacedTCBRGPackage_bridge_doubled_by_package_prefactor

/--
[generatedReplacedTCBRGPackage_valid_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_doubled_by_package_prefactor_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.generatedReplacedTCBRGPackage_valid_doubled_by_package_prefactor

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_by_package_comparison_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_by_package_comparison

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_doubled_by_package_comparison_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_doubled_by_package_comparison

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison

/--
[genMinCubicReplacedTCB_bridge_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicReplacedTCB_bridge_doubled_by_comparison_congr_pred_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicReplacedTCB_bridge_doubled_by_comparison_congr_pred

/--
[genMinCubicReplacedTCB_valid_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicReplacedTCB_valid_doubled_by_comparison_congr_pred_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicReplacedTCB_valid_doubled_by_comparison_congr_pred

/--
[genMinCubicReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_by_package_prefactor_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_by_package_prefactor

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_doubled_by_package_prefactor_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_doubled_by_package_prefactor

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_doubled_by_package_comparison_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_doubled_by_package_comparison

/--
[genBoundedCaseReplacedTCBRGPackage_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_doubled_by_package_comparison_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_doubled_by_package_comparison

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison

/--
[genBoundedCaseReplacedTCB_bridge_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCB_bridge_doubled_by_comparison_congr_pred_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCB_bridge_doubled_by_comparison_congr_pred

/--
[genBoundedCaseReplacedTCB_valid_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCB_valid_doubled_by_comparison_congr_pred_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCB_valid_doubled_by_comparison_congr_pred

/--
[genBoundedCaseReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_doubled_by_package_prefactor_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_doubled_by_package_prefactor

/--
[genBoundedCaseReplacedTCBRGPackage_valid_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_doubled_by_package_prefactor_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_doubled_by_package_prefactor

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor

/--
[genCubicClassReplacedTCBRGPackage_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_doubled_by_package_comparison_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_doubled_by_package_comparison

/--
[genCubicClassReplacedTCBRGPackage_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_doubled_by_package_comparison_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCBRGPackage_valid_doubled_by_package_comparison

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_comparison

/--
[genCubicClassReplacedTCB_bridge_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCB_bridge_doubled_by_comparison_congr_pred_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCB_bridge_doubled_by_comparison_congr_pred

/--
[genCubicClassReplacedTCB_valid_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCB_valid_doubled_by_comparison_congr_pred_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCB_valid_doubled_by_comparison_congr_pred

/--
[genCubicClassReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCB_hasCriticalNu_doubled_by_comparison_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_bridge_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_doubled_by_package_prefactor_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_doubled_by_package_prefactor

/--
[genCubicClassReplacedTCBRGPackage_valid_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_doubled_by_package_prefactor_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCBRGPackage_valid_doubled_by_package_prefactor

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) (fun β => halfThirdScalingDoublePrefactor β * halfThirdScalingCorrelationLength β) (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_by_package_prefactor

/--
[geometricTailCorrelationLength_eventually_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma geometricTailCorrelationLength_eventually_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), 0 < geometricTailCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.geometricTailCorrelationLength_eventually_pos

/--
[geometricTailCorrelationLength_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma geometricTailCorrelationLength_exact_power_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), geometricTailCorrelationLength β = Real.exp (-geometricTailWitnessPackage.certificate.predictedExponent * Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.geometricTailCorrelationLength_exact_power

/--
[geometricTailWitnessBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessBridge_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.geometricTailWitnessBridge

/--
[doubledGeometricTailCorrelationLength_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma doubledGeometricTailCorrelationLength_comparable_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), (2 : ℝ) * geometricTailCorrelationLength β ≤ doubledGeometricTailCorrelationLength β ∧ doubledGeometricTailCorrelationLength β ≤ (2 : ℝ) * geometricTailCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.doubledGeometricTailCorrelationLength_comparable

/--
[geometricTailWitness_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_doubled_by_package_comparison_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge doubledGeometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.geometricTailWitness_bridge_doubled_by_package_comparison

/--
[geometricTailWitness_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_doubled_by_package_comparison_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid doubledGeometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.geometricTailWitness_valid_doubled_by_package_comparison

/--
[geometricTailWitness_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) doubledGeometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.geometricTailWitness_hasCriticalNu_doubled_by_package_comparison

/--
[contributionSplitInfiniteTailCorrelationLength_eventually_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTailCorrelationLength_eventually_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), 0 < contributionSplitInfiniteTailCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.contributionSplitInfiniteTailCorrelationLength_eventually_pos

/--
[contributionSplitInfiniteTailCorrelationLength_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTailCorrelationLength_exact_power_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), contributionSplitInfiniteTailCorrelationLength β = Real.exp (-contributionSplitAsInfiniteTailPackage.certificate.predictedExponent * Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.contributionSplitInfiniteTailCorrelationLength_exact_power

/--
[contributionSplitInfiniteTailPackageBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTailPackageBridge_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge contributionSplitInfiniteTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.contributionSplitInfiniteTailPackageBridge

/--
[doubledContributionSplitInfiniteTailCorrelationLength_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma doubledContributionSplitInfiniteTailCorrelationLength_comparable_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), (2 : ℝ) * contributionSplitInfiniteTailCorrelationLength β ≤ doubledContributionSplitInfiniteTailCorrelationLength β ∧ doubledContributionSplitInfiniteTailCorrelationLength β ≤ (2 : ℝ) * contributionSplitInfiniteTailCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.doubledContributionSplitInfiniteTailCorrelationLength_comparable

/--
[contributionSplitInfiniteTail_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_bridge_doubled_by_package_comparison_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge doubledContributionSplitInfiniteTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.contributionSplitInfiniteTail_bridge_doubled_by_package_comparison

/--
[contributionSplitInfiniteTail_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_valid_doubled_by_package_comparison_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.Valid doubledContributionSplitInfiniteTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.contributionSplitInfiniteTail_valid_doubled_by_package_comparison

/--
[contributionSplitInfiniteTail_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) doubledContributionSplitInfiniteTailCorrelationLength contributionSplitAsInfiniteTailPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.contributionSplitInfiniteTail_hasCriticalNu_doubled_by_package_comparison

/--
[zeroStableKeyTableWitnessCorrelationLength_eventually_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessCorrelationLength_eventually_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), 0 < zeroStableKeyTableWitnessCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroStableKeyTableWitnessCorrelationLength_eventually_pos

/--
[zeroStableKeyTableWitnessCorrelationLength_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessCorrelationLength_exact_power_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), zeroStableKeyTableWitnessCorrelationLength β = Real.exp (-zeroStableKeyTableWitnessPackage.certificate.predictedExponent * Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroStableKeyTableWitnessCorrelationLength_exact_power

/--
[zeroStableKeyTableWitnessBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessBridge_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroStableKeyTableWitnessBridge

/--
[doubledZeroStableKeyTableWitnessCorrelationLength_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma doubledZeroStableKeyTableWitnessCorrelationLength_comparable_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), (2 : ℝ) * zeroStableKeyTableWitnessCorrelationLength β ≤ doubledZeroStableKeyTableWitnessCorrelationLength β ∧ doubledZeroStableKeyTableWitnessCorrelationLength β ≤ (2 : ℝ) * zeroStableKeyTableWitnessCorrelationLength β := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.doubledZeroStableKeyTableWitnessCorrelationLength_comparable

/--
[zeroStableKeyTableWitness_bridge_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_doubled_by_package_comparison_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge doubledZeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroStableKeyTableWitness_bridge_doubled_by_package_comparison

/--
[zeroStableKeyTableWitness_valid_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_doubled_by_package_comparison_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid doubledZeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroStableKeyTableWitness_valid_doubled_by_package_comparison

/--
[zeroStableKeyTableWitness_hasCriticalNu_doubled_by_package_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_doubled_by_package_comparison_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) doubledZeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageComparisonBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_doubled_by_package_comparison


-- created on 2026-10-23
