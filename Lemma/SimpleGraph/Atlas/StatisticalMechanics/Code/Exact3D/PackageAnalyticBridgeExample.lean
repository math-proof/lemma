import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PackageAnalyticBridgeExample.Part5
open StatMech StatMech.Exact3D StatMech.Exact3D.PackageAnalyticBridgeExample


/--
[contributionSplitWitnessCorrelationLength_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessCorrelationLength_exact_power_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), contributionSplitWitnessCorrelationLength β = Real.exp (-contributionSplitWitnessPackage.certificate.predictedExponent * Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitWitnessCorrelationLength_exact_power

/--
[contributionSplitWitness_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_analyticInputs_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitWitness_bridge_from_analyticInputs

/--
[contributionSplitWitness_bridge_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_analyticInputs_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitWitness_bridge_from_analyticInputs_congr_pred

/--
[contributionSplitWitness_valid_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_valid_from_analyticInputs_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.Valid contributionSplitWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitWitness_valid_from_analyticInputs_congr_pred

/--
[contributionSplitWitness_hasCriticalNu_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_hasCriticalNu_from_analyticInputs_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitWitnessCorrelationLength contributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitWitness_hasCriticalNu_from_analyticInputs_congr_pred

/--
[contributionSplitWitness_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_valid_from_analyticInputs_eq :
-- imply
  contributionSplitWitnessPackage.certificate.Valid contributionSplitWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitWitness_valid_from_analyticInputs

/--
[contributionSplitWitness_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitWitnessCorrelationLength contributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitWitness_hasCriticalNu_from_analyticInputs

/--
[geometricTailWitness_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_analyticInputs_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.geometricTailWitness_bridge_from_analyticInputs

/--
[geometricTailWitness_bridge_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_analyticInputs_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.geometricTailWitness_bridge_from_analyticInputs_congr_pred

/--
[geometricTailWitness_valid_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_from_analyticInputs_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.geometricTailWitness_valid_from_analyticInputs_congr_pred

/--
[geometricTailWitness_hasCriticalNu_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_from_analyticInputs_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.geometricTailWitness_hasCriticalNu_from_analyticInputs_congr_pred

/--
[geometricTailWitness_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_from_analyticInputs_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.geometricTailWitness_valid_from_analyticInputs

/--
[geometricTailWitness_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.geometricTailWitness_hasCriticalNu_from_analyticInputs

/--
[contributionSplitInfiniteTail_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_bridge_from_analyticInputs_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge contributionSplitInfiniteTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitInfiniteTail_bridge_from_analyticInputs

/--
[contributionSplitInfiniteTail_bridge_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_bridge_from_analyticInputs_congr_pred_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge contributionSplitInfiniteTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitInfiniteTail_bridge_from_analyticInputs_congr_pred

/--
[contributionSplitInfiniteTail_valid_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_valid_from_analyticInputs_congr_pred_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.Valid contributionSplitInfiniteTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitInfiniteTail_valid_from_analyticInputs_congr_pred

/--
[contributionSplitInfiniteTail_hasCriticalNu_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_hasCriticalNu_from_analyticInputs_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitInfiniteTailCorrelationLength contributionSplitAsInfiniteTailPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitInfiniteTail_hasCriticalNu_from_analyticInputs_congr_pred

/--
[contributionSplitInfiniteTail_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_valid_from_analyticInputs_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.Valid contributionSplitInfiniteTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitInfiniteTail_valid_from_analyticInputs

/--
[contributionSplitInfiniteTail_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma contributionSplitInfiniteTail_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitInfiniteTailCorrelationLength contributionSplitAsInfiniteTailPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.contributionSplitInfiniteTail_hasCriticalNu_from_analyticInputs

/--
[zeroStableKeyTableWitness_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_analyticInputs_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroStableKeyTableWitness_bridge_from_analyticInputs

/--
[zeroStableKeyTableWitness_bridge_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_analyticInputs_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroStableKeyTableWitness_bridge_from_analyticInputs_congr_pred

/--
[zeroStableKeyTableWitness_valid_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_from_analyticInputs_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroStableKeyTableWitness_valid_from_analyticInputs_congr_pred

/--
[zeroStableKeyTableWitness_hasCriticalNu_from_analyticInputs_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_from_analyticInputs_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_from_analyticInputs_congr_pred

/--
[zeroStableKeyTableWitness_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_from_analyticInputs_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroStableKeyTableWitness_valid_from_analyticInputs

/--
[zeroStableKeyTableWitness_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_from_analyticInputs

/--
[halfThirdScalingHyperbolic_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_analyticInputs_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_bridge_from_analyticInputs

/--
[halfThirdScalingHyperbolic_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_analyticInputs_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_valid_from_analyticInputs

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_analyticInputs

/--
[halfThirdScalingHyperbolic_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_prefactorInputs_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_bridge_from_prefactorInputs

/--
[halfThirdScalingHyperbolic_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_prefactorInputs_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_valid_from_prefactorInputs

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_prefactorInputs

/--
[halfThirdScalingHyperbolic_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_massInputs_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_bridge_from_massInputs

/--
[halfThirdScalingHyperbolic_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_massInputs_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_valid_from_massInputs

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_massInputs

/--
[halfThirdScalingBlockRGPackage_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_analyticInputs_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_analyticInputs

/--
[halfThirdScalingBlockRGPackage_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_prefactorInputs_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_prefactorInputs

/--
[halfThirdScalingBlockRGPackage_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_analyticInputs_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_valid_from_analyticInputs

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_analyticInputs

/--
[halfThirdScalingBlockRGPackage_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_prefactorInputs_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_valid_from_prefactorInputs

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_prefactorInputs

/--
[halfThirdScalingBlockRGPackage_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_massInputs_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_massInputs

/--
[halfThirdScalingBlockRGPackage_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_massInputs_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_valid_from_massInputs

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_massInputs

/--
[halfThirdScalingClosedBall_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_predictedExponent_eq_rg_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_predictedExponent_eq_rg

/--
[halfThirdScalingClosedBall_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_analyticInputs_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_bridge_from_analyticInputs

/--
[halfThirdScalingClosedBall_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_prefactorInputs_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_bridge_from_prefactorInputs

/--
[halfThirdScalingClosedBall_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_massInputs_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_bridge_from_massInputs

/--
[halfThirdScalingClosedBall_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_analyticInputs_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_valid_from_analyticInputs

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_analyticInputs

/--
[halfThirdScalingClosedBall_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_prefactorInputs_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_valid_from_prefactorInputs

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_prefactorInputs

/--
[halfThirdScalingClosedBall_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_massInputs_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_valid_from_massInputs

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_massInputs

/--
[zeroTableClosedBallRGPackage_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_analyticInputs_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_bridge_from_analyticInputs

/--
[zeroTableClosedBallRGPackage_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_analyticInputs_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_valid_from_analyticInputs

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_analyticInputs

/--
[zeroTableClosedBallRGPackage_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_prefactorInputs_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_bridge_from_prefactorInputs

/--
[zeroTableClosedBallRGPackage_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_prefactorInputs_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_valid_from_prefactorInputs

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_prefactorInputs

/--
[zeroTableClosedBallRGPackage_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_massInputs_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_bridge_from_massInputs

/--
[zeroTableClosedBallRGPackage_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_massInputs_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_valid_from_massInputs

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_massInputs

/--
[generatedReplacedTCBRGPackage_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_analyticInputs_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_bridge_from_analyticInputs

/--
[generatedReplacedTCBRGPackage_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_analyticInputs_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_valid_from_analyticInputs

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_analyticInputs_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_analyticInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_analyticInputs_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_analyticInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_analyticInputs_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_analyticInputs

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_analyticInputs_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_analyticInputs

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_analyticInputs_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_analyticInputs

/--
[genCubicClassReplacedTCBRGPackage_valid_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_analyticInputs_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_analyticInputs

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_analyticInputs

/--
[generatedReplacedTCBRGPackage_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_prefactorInputs_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_bridge_from_prefactorInputs

/--
[generatedReplacedTCBRGPackage_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_prefactorInputs_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_valid_from_prefactorInputs

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_prefactorInputs_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_prefactorInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_prefactorInputs_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_prefactorInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_prefactorInputs_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_prefactorInputs

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_prefactorInputs_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_prefactorInputs

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_prefactorInputs_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_prefactorInputs

/--
[genCubicClassReplacedTCBRGPackage_valid_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_prefactorInputs_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_prefactorInputs

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_prefactorInputs

/--
[generatedReplacedTCBRGPackage_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_massInputs_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_bridge_from_massInputs

/--
[generatedReplacedTCBRGPackage_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_massInputs_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_valid_from_massInputs

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_massInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_massInputs_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_massInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_massInputs_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_massInputs

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massInputs

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_massInputs_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_massInputs

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_massInputs_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_massInputs

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massInputs

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_massInputs_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_massInputs

/--
[genCubicClassReplacedTCBRGPackage_valid_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_massInputs_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_massInputs

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageAnalyticBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massInputs_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageAnalyticBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massInputs


-- created on 2026-10-23
