import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.PackageFKBridgeExample
open StatMech StatMech.Exact3D StatMech.Exact3D.PackageFKBridgeExample


/--
[blockRGFKToyCorrelationLength_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma blockRGFKToyCorrelationLength_exact_power_eq :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), blockRGFKToyCorrelationLength p = Real.exp (-((halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent) * Real.log ((ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))).betaC - p)) := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.blockRGFKToyCorrelationLength_exact_power

/--
[blockRGFKToy_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma blockRGFKToy_hasCriticalNu_eq :
-- imply
  HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) blockRGFKToyCorrelationLength (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.blockRGFKToy_hasCriticalNu

/--
[blockRGFKComposedIsingCorrelationLength_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma blockRGFKComposedIsingCorrelationLength_eventually_eq_eq :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), blockRGFKComposedIsingCorrelationLength β = blockRGFKToyCorrelationLength (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.blockRGFKComposedIsingCorrelationLength_eventually_eq

/--
[contributionSplitWitnessPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[contributionSplitWitnessPackage_bridge_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_fkPowerTarget_congr_pred_eq :
-- imply
  ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_bridge_from_fkPowerTarget_congr_pred

/--
[contributionSplitWitnessPackage_valid_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_from_fkPowerTarget_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_valid_from_fkPowerTarget_congr_pred

/--
[contributionSplitWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred

/--
[contributionSplitWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred

/--
[contributionSplitWitnessPackage_valid_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_valid_from_fkMassPowerTarget_congr_pred

/--
[contributionSplitWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred

/--
[contributionSplitWitnessPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (contributionSplitWitnessPackage.retarget Ising3DModel).certificate.Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_valid_from_fk_pOfBeta_congr_pred

/--
[contributionSplitWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.contributionSplitWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[geometricTailWitnessPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[geometricTailWitnessPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_valid_from_fk_pOfBeta_congr_pred

/--
[geometricTailWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[geometricTailWitnessPackage_bridge_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_bridge_from_fkPowerTarget_congr_pred_eq :
-- imply
  ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_bridge_from_fkPowerTarget_congr_pred

/--
[geometricTailWitnessPackage_valid_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_from_fkPowerTarget_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_valid_from_fkPowerTarget_congr_pred

/--
[geometricTailWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred

/--
[geometricTailWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred

/--
[geometricTailWitnessPackage_valid_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  (geometricTailWitnessPackage.retarget Ising3DModel).certificate.Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_valid_from_fkMassPowerTarget_congr_pred

/--
[geometricTailWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.geometricTailWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[zeroStableKeyTableWitnessPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_valid_from_fk_pOfBeta_congr_pred

/--
[zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[zeroStableKeyTableWitnessPackage_bridge_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_bridge_from_fkPowerTarget_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_bridge_from_fkPowerTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_valid_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_valid_from_fkPowerTarget_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_valid_from_fkPowerTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fkPowerTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_bridge_from_fkMassPowerTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_valid_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_valid_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate.Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_valid_from_fkMassPowerTarget_congr_pred

/--
[zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroStableKeyTableWitnessPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingHyperbolic_bridge_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_fkMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_fkMassTarget_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingHyperbolic_bridge_from_fkMassTarget_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_fkMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_fkMassTarget_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingHyperbolic_valid_from_fkMassTarget_congr_pred

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_fkMassTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_fkMassTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_fkMassTarget_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingHyperbolic_valid_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingBlockRGPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingBlockRGPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingBlockRGPackage_valid_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingClosedBall_bridge_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingClosedBall_valid_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_fkMassPowerTarget_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroTableClosedBallRGPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroTableClosedBallRGPackage_valid_from_fk_pOfBeta_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroTableClosedBallRGPackage_valid_from_fkMassPowerTarget_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroTableClosedBallRGPackage_bridge_from_fkMassPowerTarget_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.generatedReplacedTCBRGPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.generatedReplacedTCBRGPackage_valid_from_fk_pOfBeta_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.generatedReplacedTCBRGPackage_valid_from_fkMassPowerTarget_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.generatedReplacedTCBRGPackage_bridge_from_fkMassPowerTarget_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred

/--
[genMinCubicKeyReplacedPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genMinCubicKeyReplacedPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[genMinCubicKeyReplacedPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genMinCubicKeyReplacedPackage_valid_from_fk_pOfBeta_congr_pred

/--
[genMinCubicKeyReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genMinCubicKeyReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[genMinCubicKeyReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genMinCubicKeyReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred

/--
[genMinCubicKeyReplacedPackage_valid_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_valid_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genMinCubicKeyReplacedPackage_valid_from_fkMassPowerTarget_congr_pred

/--
[genMinCubicKeyReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genMinCubicKeyReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred

/--
[genBoundedCaseReplacedPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genBoundedCaseReplacedPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[genBoundedCaseReplacedPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genBoundedCaseReplacedPackage_valid_from_fk_pOfBeta_congr_pred

/--
[genBoundedCaseReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genBoundedCaseReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[genBoundedCaseReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genBoundedCaseReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred

/--
[genBoundedCaseReplacedPackage_valid_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_valid_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genBoundedCaseReplacedPackage_valid_from_fkMassPowerTarget_congr_pred

/--
[genBoundedCaseReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genBoundedCaseReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred

/--
[genCubicClassReplacedPackage_bridge_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_bridge_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genCubicClassReplacedPackage_bridge_from_fk_pOfBeta_congr_pred

/--
[genCubicClassReplacedPackage_valid_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_valid_from_fk_pOfBeta_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid blockRGFKComposedIsingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genCubicClassReplacedPackage_valid_from_fk_pOfBeta_congr_pred

/--
[genCubicClassReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel blockRGFKComposedIsingCorrelationLength ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genCubicClassReplacedPackage_hasCriticalNu_from_fk_pOfBeta_congr_pred

/--
[genCubicClassReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).RGToExponentBridge TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genCubicClassReplacedPackage_bridge_from_fkMassPowerTarget_congr_pred

/--
[genCubicClassReplacedPackage_valid_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_valid_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).Valid TFKM.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genCubicClassReplacedPackage_valid_from_fkMassPowerTarget_congr_pred

/--
[genCubicClassReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageFKBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred_eq :
-- imply
  HasCriticalNu Ising3DModel TFKM.isingCorrelationLength ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageFKBridgeExample.genCubicClassReplacedPackage_hasCriticalNu_from_fkMassPowerTarget_congr_pred


-- created on 2026-10-23
