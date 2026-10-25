import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PackageIsingBridgeExample
open StatMech StatMech.Exact3D StatMech.Exact3D.PackageIsingBridgeExample


/--
[contributionSplitWitnessPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_bridge_from_isingTarget_congr_pred

/--
[contributionSplitWitnessPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_valid_from_isingTarget_congr_pred

/--
[contributionSplitWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[geometricTailWitnessPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_bridge_from_isingTarget_congr_pred

/--
[geometricTailWitnessPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_valid_from_isingTarget_congr_pred

/--
[geometricTailWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_bridge_from_isingTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_valid_from_isingTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_isingTarget_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_bridge_from_isingTarget_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_isingTarget_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_valid_from_isingTarget_congr_pred

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_isingTarget_congr_pred

/--
[halfThirdScalingBlockRGPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_isingTarget_congr_pred

/--
[halfThirdScalingBlockRGPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_valid_from_isingTarget_congr_pred

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_isingTarget_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_bridge_from_isingTarget_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_isingTarget_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_valid_from_isingTarget_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_isingTarget_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_bridge_from_isingTarget_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_valid_from_isingTarget_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_bridge_from_isingTarget_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_valid_from_isingTarget_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[genMinCubicKeyReplacedPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_bridge_from_isingTarget_congr_pred

/--
[genMinCubicKeyReplacedPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_valid_from_isingTarget_congr_pred

/--
[genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[genBoundedCaseReplacedPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_bridge_from_isingTarget_congr_pred

/--
[genBoundedCaseReplacedPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_valid_from_isingTarget_congr_pred

/--
[genBoundedCaseReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[genCubicClassReplacedPackage_bridge_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_bridge_from_isingTarget_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_bridge_from_isingTarget_congr_pred

/--
[genCubicClassReplacedPackage_valid_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_valid_from_isingTarget_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_valid_from_isingTarget_congr_pred

/--
[genCubicClassReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_hasCriticalNu_from_isingTarget_congr_pred

/--
[contributionSplitWitnessPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_bridge_from_isingCoordinate_congr_pred

/--
[contributionSplitWitnessPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[contributionSplitWitnessPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_valid_from_isingCoordinate_congr_pred

/--
[contributionSplitWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[contributionSplitWitnessPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_valid_from_isingMassCoordinate_congr_pred

/--
[contributionSplitWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[geometricTailWitnessPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_bridge_from_isingCoordinate_congr_pred

/--
[geometricTailWitnessPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_valid_from_isingCoordinate_congr_pred

/--
[geometricTailWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[geometricTailWitnessPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[geometricTailWitnessPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_valid_from_isingMassCoordinate_congr_pred

/--
[geometricTailWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[zeroStableKeyTableWitnessPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_bridge_from_isingCoordinate_congr_pred

/--
[zeroStableKeyTableWitnessPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_valid_from_isingCoordinate_congr_pred

/--
[zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[zeroStableKeyTableWitnessPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[zeroStableKeyTableWitnessPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_valid_from_isingMassCoordinate_congr_pred

/--
[zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_bridge_from_isingCoordinate_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_valid_from_isingCoordinate_congr_pred

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_bridge_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_valid_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingBlockRGPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_isingCoordinate_congr_pred

/--
[halfThirdScalingBlockRGPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_valid_from_isingCoordinate_congr_pred

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[halfThirdScalingBlockRGPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingBlockRGPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_valid_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_bridge_from_isingCoordinate_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_valid_from_isingCoordinate_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_bridge_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_valid_from_isingMassCoordinate_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_bridge_from_isingCoordinate_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_valid_from_isingCoordinate_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_valid_from_isingMassCoordinate_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_bridge_from_isingCoordinate_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_valid_from_isingCoordinate_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_valid_from_isingMassCoordinate_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[genMinCubicKeyReplacedPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_bridge_from_isingCoordinate_congr_pred

/--
[genMinCubicKeyReplacedPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_valid_from_isingCoordinate_congr_pred

/--
[genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[genMinCubicKeyReplacedPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[genMinCubicKeyReplacedPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_valid_from_isingMassCoordinate_congr_pred

/--
[genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[genBoundedCaseReplacedPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_bridge_from_isingCoordinate_congr_pred

/--
[genBoundedCaseReplacedPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_valid_from_isingCoordinate_congr_pred

/--
[genBoundedCaseReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[genBoundedCaseReplacedPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[genBoundedCaseReplacedPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_valid_from_isingMassCoordinate_congr_pred

/--
[genBoundedCaseReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[genCubicClassReplacedPackage_bridge_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_bridge_from_isingCoordinate_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_bridge_from_isingCoordinate_congr_pred

/--
[genCubicClassReplacedPackage_valid_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_valid_from_isingCoordinate_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_valid_from_isingCoordinate_congr_pred

/--
[genCubicClassReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TC.scaffold.correlationLength ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_hasCriticalNu_from_isingCoordinate_congr_pred

/--
[genCubicClassReplacedPackage_bridge_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_bridge_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_bridge_from_isingMassCoordinate_congr_pred

/--
[genCubicClassReplacedPackage_valid_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_valid_from_isingMassCoordinate_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TMC.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_valid_from_isingMassCoordinate_congr_pred

/--
[genCubicClassReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TMC.scaffold.correlationLength ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_hasCriticalNu_from_isingMassCoordinate_congr_pred

/--
[contributionSplitWitnessPackage_bridge_from_isingMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_isingMassPowerTarget_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_bridge_from_isingMassPowerTarget_congr_pred

/--
[contributionSplitWitnessPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_bridge_from_isingMassPower_congr_pred

/--
[contributionSplitWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[contributionSplitWitnessPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_valid_from_isingMassPower_congr_pred

/--
[contributionSplitWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[contributionSplitWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[contributionSplitWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.contributionSplitWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[geometricTailWitnessPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_bridge_from_isingMassPower_congr_pred

/--
[geometricTailWitnessPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_valid_from_isingMassPower_congr_pred

/--
[geometricTailWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[geometricTailWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[geometricTailWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[geometricTailWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.geometricTailWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[zeroStableKeyTableWitnessPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_bridge_from_isingMassPower_congr_pred

/--
[zeroStableKeyTableWitnessPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_valid_from_isingMassPower_congr_pred

/--
[zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[zeroStableKeyTableWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[zeroStableKeyTableWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[zeroStableKeyTableWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroStableKeyTableWitnessPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_isingMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_isingMassTarget_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_bridge_from_isingMassTarget_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_isingMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_isingMassTarget_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_valid_from_isingMassTarget_congr_pred

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassTarget_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_bridge_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_bridge_from_isingMassPower_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_isingMassPower_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_valid_from_isingMassPower_congr_pred

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_isingMassPower_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_valid_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingBlockRGPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_isingMassPower_congr_pred

/--
[halfThirdScalingBlockRGPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_valid_from_isingMassPower_congr_pred

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[halfThirdScalingBlockRGPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingBlockRGPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_isingMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_isingMassTarget_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_bridge_from_isingMassTarget_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_isingMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_isingMassTarget_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_valid_from_isingMassTarget_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_isingMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_isingMassTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_isingMassTarget_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_bridge_from_isingMassPower_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_bridge_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_isingMassPower_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_valid_from_isingMassPower_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_isingMassPower_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_valid_from_freeMassPowerToPlus_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_bridge_from_isingMassPower_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_valid_from_isingMassPower_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_bridge_from_isingMassPower_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_valid_from_isingMassPower_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[genMinCubicKeyReplacedPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_bridge_from_isingMassPower_congr_pred

/--
[genMinCubicKeyReplacedPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_valid_from_isingMassPower_congr_pred

/--
[genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[genMinCubicKeyReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[genMinCubicKeyReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[genMinCubicKeyReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genMinCubicKeyReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[genBoundedCaseReplacedPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_bridge_from_isingMassPower_congr_pred

/--
[genBoundedCaseReplacedPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_valid_from_isingMassPower_congr_pred

/--
[genBoundedCaseReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[genBoundedCaseReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[genBoundedCaseReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[genBoundedCaseReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genBoundedCaseReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred

/--
[genCubicClassReplacedPackage_bridge_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_bridge_from_isingMassPower_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_bridge_from_isingMassPower_congr_pred

/--
[genCubicClassReplacedPackage_valid_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_valid_from_isingMassPower_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_valid_from_isingMassPower_congr_pred

/--
[genCubicClassReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TM.correlationLength ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_hasCriticalNu_from_isingMassPower_congr_pred

/--
[genCubicClassReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_bridge_from_freeMassPowerToPlus_congr_pred

/--
[genCubicClassReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TFM.correlationLength := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_valid_from_freeMassPowerToPlus_congr_pred

/--
[genCubicClassReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageIsingBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFM.correlationLength ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageIsingBridgeExample.genCubicClassReplacedPackage_hasCriticalNu_from_freeMassPowerToPlus_congr_pred


-- created on 2026-10-23
