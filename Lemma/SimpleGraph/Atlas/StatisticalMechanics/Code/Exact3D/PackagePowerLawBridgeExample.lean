import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PackagePowerLawBridgeExample
open StatMech StatMech.Exact3D StatMech.Exact3D.PackagePowerLawBridgeExample


/--
[contributionSplitWitnessPowerLawCorrelationLength_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPowerLawCorrelationLength_exact_power_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), contributionSplitWitnessPowerLawCorrelationLength β = (1 : ℝ) * Real.exp (-contributionSplitWitnessPackage.certificate.predictedExponent * Real.log ((ToyCriticalModel exampleScale 3).betaC - β)) := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitnessPowerLawCorrelationLength_exact_power

/--
[contributionSplitWitness_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_powerLaw_wrapper_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_powerLaw_wrapper

/--
[contributionSplitWitness_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_variablePowerLaw_wrapper

/--
[contributionSplitWitness_bridge_from_powerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_powerLaw_on_Ioo_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_powerLaw_on_Ioo

/--
[contributionSplitWitness_bridge_from_variablePowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_variablePowerLaw_on_Ioo_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_variablePowerLaw_on_Ioo

/--
[contributionSplitWitness_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_powerLaw_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_powerLaw_congr_pred

/--
[contributionSplitWitness_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_variablePowerLaw_congr_pred

/--
[contributionSplitWitness_bridge_from_massPowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_massPowerLaw_on_Ioo_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_massPowerLaw_on_Ioo

/--
[contributionSplitWitness_bridge_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_powerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_valid_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_valid_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.Valid contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_valid_from_powerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitWitnessPowerLawCorrelationLength contributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.Valid contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitWitnessPowerLawCorrelationLength contributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_valid_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_valid_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  contributionSplitWitnessPackage.certificate.Valid contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_valid_from_massPowerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitWitnessPowerLawCorrelationLength contributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred

/--
[contributionSplitWitness_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_valid_from_powerLaw_wrapper_eq :
-- imply
  contributionSplitWitnessPackage.certificate.Valid contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_valid_from_powerLaw_wrapper

/--
[contributionSplitWitness_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitWitnessPowerLawCorrelationLength contributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_hasCriticalNu_from_powerLaw_wrapper

/--
[contributionSplitWitness_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  contributionSplitWitnessPackage.certificate.Valid contributionSplitWitnessPowerLawCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_valid_from_variablePowerLaw_wrapper

/--
[contributionSplitWitness_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma contributionSplitWitness_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) contributionSplitWitnessPowerLawCorrelationLength contributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.contributionSplitWitness_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[geometricTailWitness_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_powerLaw_wrapper_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_powerLaw_wrapper

/--
[geometricTailWitness_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_variablePowerLaw_wrapper

/--
[geometricTailWitness_bridge_from_powerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_powerLaw_on_Ioo_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_powerLaw_on_Ioo

/--
[geometricTailWitness_bridge_from_variablePowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_variablePowerLaw_on_Ioo_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_variablePowerLaw_on_Ioo

/--
[geometricTailWitness_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_powerLaw_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_powerLaw_congr_pred

/--
[geometricTailWitness_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_variablePowerLaw_congr_pred

/--
[geometricTailWitness_bridge_from_massPowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_massPowerLaw_on_Ioo_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_massPowerLaw_on_Ioo

/--
[geometricTailWitness_bridge_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_powerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_valid_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_valid_from_powerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_valid_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_valid_from_massPowerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred

/--
[geometricTailWitness_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_from_powerLaw_wrapper_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_valid_from_powerLaw_wrapper

/--
[geometricTailWitness_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_hasCriticalNu_from_powerLaw_wrapper

/--
[geometricTailWitness_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  geometricTailWitnessPackage.certificate.Valid geometricTailCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_valid_from_variablePowerLaw_wrapper

/--
[geometricTailWitness_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma geometricTailWitness_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) geometricTailCorrelationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.geometricTailWitness_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[zeroStableKeyTableWitness_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_powerLaw_wrapper_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_powerLaw_wrapper

/--
[zeroStableKeyTableWitness_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_variablePowerLaw_wrapper

/--
[zeroStableKeyTableWitness_bridge_from_powerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_powerLaw_on_Ioo_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_powerLaw_on_Ioo

/--
[zeroStableKeyTableWitness_bridge_from_variablePowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_variablePowerLaw_on_Ioo_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_variablePowerLaw_on_Ioo

/--
[zeroStableKeyTableWitness_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_powerLaw_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_powerLaw_congr_pred

/--
[zeroStableKeyTableWitness_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_variablePowerLaw_congr_pred

/--
[zeroStableKeyTableWitness_bridge_from_massPowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_massPowerLaw_on_Ioo_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_massPowerLaw_on_Ioo

/--
[zeroStableKeyTableWitness_bridge_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_powerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_variablePowerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.RGToExponentBridge zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_bridge_from_massPowerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_valid_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_valid_from_powerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_from_powerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_valid_from_variablePowerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_from_variablePowerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_valid_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_valid_from_massPowerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_from_massPowerLaw_on_Ioo_congr_pred

/--
[zeroStableKeyTableWitness_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_from_powerLaw_wrapper_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_valid_from_powerLaw_wrapper

/--
[zeroStableKeyTableWitness_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_from_powerLaw_wrapper

/--
[zeroStableKeyTableWitness_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  zeroStableKeyTableWitnessPackage.certificate.Valid zeroStableKeyTableWitnessCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_valid_from_variablePowerLaw_wrapper

/--
[zeroStableKeyTableWitness_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitness_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroStableKeyTableWitnessCorrelationLength zeroStableKeyTableWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroStableKeyTableWitness_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[halfThirdScalingHyperbolic_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_powerLaw_wrapper_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_powerLaw_wrapper

/--
[halfThirdScalingHyperbolic_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_powerLaw_wrapper_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_valid_from_powerLaw_wrapper

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_powerLaw_wrapper

/--
[halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_wrapper

/--
[halfThirdScalingHyperbolic_bridge_from_powerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_powerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_powerLaw_on_Ioo

/--
[halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_on_Ioo

/--
[halfThirdScalingHyperbolic_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_valid_from_variablePowerLaw_wrapper

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[halfThirdScalingHyperbolic_bridge_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_massPowerLaw_wrapper_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_massPowerLaw_wrapper

/--
[halfThirdScalingHyperbolic_bridge_from_massPowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_massPowerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_massPowerLaw_on_Ioo

/--
[halfThirdScalingHyperbolic_bridge_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_powerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_variablePowerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingHyperbolic_bridge_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_bridge_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_bridge_from_massPowerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingHyperbolic_valid_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_valid_from_massPowerLaw_wrapper_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_valid_from_massPowerLaw_wrapper

/--
[halfThirdScalingHyperbolic_hasCriticalNu_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_hasCriticalNu_from_massPowerLaw_wrapper_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingHyperbolic_hasCriticalNu_from_massPowerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_powerLaw_wrapper_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_powerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_powerLaw_wrapper_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_valid_from_powerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_powerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_bridge_from_powerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_powerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_powerLaw_on_Ioo

/--
[halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_on_Ioo

/--
[halfThirdScalingBlockRGPackage_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_valid_from_variablePowerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_wrapper_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_on_Ioo

/--
[halfThirdScalingBlockRGPackage_bridge_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_powerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_variablePowerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_bridge_from_massPowerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingBlockRGPackage_valid_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_valid_from_massPowerLaw_wrapper_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_valid_from_massPowerLaw_wrapper

/--
[halfThirdScalingBlockRGPackage_hasCriticalNu_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_hasCriticalNu_from_massPowerLaw_wrapper_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingBlockRGPackage_hasCriticalNu_from_massPowerLaw_wrapper

/--
[halfThirdScalingClosedBall_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_predictedExponent_eq_rg_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent = halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_predictedExponent_eq_rg

/--
[halfThirdScalingClosedBall_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_powerLaw_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_powerLaw_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_powerLaw_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_valid_from_powerLaw_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_powerLaw_congr_pred_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_powerLaw_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_variablePowerLaw_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_powerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_powerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_powerLaw_on_Ioo

/--
[halfThirdScalingClosedBall_bridge_from_variablePowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_variablePowerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_variablePowerLaw_on_Ioo

/--
[halfThirdScalingClosedBall_valid_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_variablePowerLaw_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_valid_from_variablePowerLaw_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_variablePowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_variablePowerLaw_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_massPowerLaw_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_massPowerLaw_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_massPowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_massPowerLaw_on_Ioo_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_massPowerLaw_on_Ioo

/--
[halfThirdScalingClosedBall_bridge_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_powerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_variablePowerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingClosedBall_bridge_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_bridge_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_bridge_from_massPowerLaw_on_Ioo_congr_pred

/--
[halfThirdScalingClosedBall_valid_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_valid_from_massPowerLaw_congr_pred_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_valid_from_massPowerLaw_congr_pred

/--
[halfThirdScalingClosedBall_hasCriticalNu_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_hasCriticalNu_from_massPowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingCorrelationLength (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale halfThirdScalingModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.halfThirdScalingClosedBall_hasCriticalNu_from_massPowerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_predictedExponent_eq_rg_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent = halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_predictedExponent_eq_rg

/--
[generatedReplacedTCBRGPackage_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_predictedExponent_eq_rg_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent = halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_predictedExponent_eq_rg

/--
[genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent = halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_predictedExponent_eq_rg

/--
[genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent = halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_predictedExponent_eq_rg

/--
[genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent = halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_predictedExponent_eq_rg

/--
[zeroTableClosedBallRGPackage_closedBallRadius_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_closedBallRadius_nonneg_eq :
-- imply
  0 ≤ zeroTableClosedBallRGPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_closedBallRadius_nonneg

/--
[zeroTableClosedBallRGPackage_closedBallResidual_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_closedBallResidual_bound_eq :
-- imply
  (zeroTableClosedBallRGPackage.closedBallContraction.map zeroTableClosedBallRGPackage.closedBallCenter).dist zeroTableClosedBallRGPackage.closedBallCenter ≤ zeroTableClosedBallRGPackage.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_closedBallResidual_bound

/--
[generatedReplacedTCBRGPackage_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_mapsClosedBall_eq :
-- imply
  FinitePlusTailState.MapsClosedBall generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.map generatedStableKeyReplacedTableClosedBallRGPackage.closedBallCenter generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_mapsClosedBall

/--
[generatedReplacedTCBRGPackage_closedBall_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_closedBall_fixedPoint_isFixed_eq :
-- imply
  generatedStableKeyReplacedTableClosedBallRGPackage.closedBallContraction.map generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRG.closedBall.fixedPoint = generatedStableKeyReplacedTableClosedBallRGPackage.closedBallRG.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_closedBall_fixedPoint_isFixed

/--
[genMinCubicKeyReplacedTCBRGPackage_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_mapsClosedBall_eq :
-- imply
  FinitePlusTailState.MapsClosedBall genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.map genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallCenter genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_mapsClosedBall

/--
[genMinCubicKeyReplacedTCBRGPackage_closedBall_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_closedBall_fixedPoint_isFixed_eq :
-- imply
  let fp := genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallRG.closedBall.fixedPoint genMinCubicKeyReplacedTableClosedBallRGPackage.closedBallContraction.map fp = fp := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_closedBall_fixedPoint_isFixed

/--
[genBoundedCaseReplacedTCBRGPackage_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_mapsClosedBall_eq :
-- imply
  FinitePlusTailState.MapsClosedBall genBoundedCaseReplacedPackage.closedBallContraction.map genBoundedCaseReplacedPackage.closedBallCenter genBoundedCaseReplacedPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_mapsClosedBall

/--
[genBoundedCaseReplacedTCBRGPackage_closedBall_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_closedBall_fixedPoint_isFixed_eq :
-- imply
  genBoundedCaseReplacedPackage.closedBallContraction.map genBoundedCaseReplacedPackage.closedBallRG.closedBall.fixedPoint = genBoundedCaseReplacedPackage.closedBallRG.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_closedBall_fixedPoint_isFixed

/--
[genCubicClassReplacedTCBRGPackage_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_mapsClosedBall_eq :
-- imply
  FinitePlusTailState.MapsClosedBall genCubicClassReplacedPackage.closedBallContraction.map genCubicClassReplacedPackage.closedBallCenter genCubicClassReplacedPackage.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_mapsClosedBall

/--
[genCubicClassReplacedTCBRGPackage_closedBall_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_closedBall_fixedPoint_isFixed_eq :
-- imply
  genCubicClassReplacedPackage.closedBallContraction.map genCubicClassReplacedPackage.closedBallRG.closedBall.fixedPoint = genCubicClassReplacedPackage.closedBallRG.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_closedBall_fixedPoint_isFixed

/--
[zeroTableClosedBallRGPackage_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_powerLaw_wrapper_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_powerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_powerLaw_wrapper_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_bridge_from_powerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_powerLaw_wrapper_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_powerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_powerLaw_wrapper_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_powerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_powerLaw_wrapper_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_powerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_variablePowerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_massPowerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_wrapper_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_wrapper_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_powerLaw_wrapper_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_valid_from_powerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_powerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_powerLaw_wrapper_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_valid_from_powerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_powerLaw_wrapper_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_powerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_powerLaw_wrapper_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_powerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_valid_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_powerLaw_wrapper_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_powerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_variablePowerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_massPowerLaw_wrapper

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_valid_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_variablePowerLaw_wrapper_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_valid_from_variablePowerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_variablePowerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_valid_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_massPowerLaw_wrapper_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_valid_from_massPowerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_massPowerLaw_wrapper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_massPowerLaw_wrapper_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_massPowerLaw_wrapper

/--
[zeroTableClosedBallRGPackage_bridge_from_powerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_powerLaw_on_Ioo_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_powerLaw_on_Ioo

/--
[zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_on_Ioo_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_on_Ioo

/--
[zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_on_Ioo_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_on_Ioo

/--
[zeroTableClosedBallRGPackage_bridge_from_powerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_powerLaw_on_Ioo_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_powerLaw_on_Ioo_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_on_Ioo_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_on_Ioo_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_on_Ioo_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_on_Ioo_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_powerLaw_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_powerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_powerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_variablePowerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_variablePowerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_bridge_from_massPowerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_bridge_from_massPowerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_powerLaw_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_valid_from_powerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_powerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_powerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_variablePowerLaw_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_valid_from_variablePowerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_valid_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_from_massPowerLaw_congr_pred_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_valid_from_massPowerLaw_congr_pred

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.zeroTableClosedBallRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_powerLaw_congr_pred_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_valid_from_powerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.generatedReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_powerLaw_congr_pred_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_powerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_powerLaw_congr_pred_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_powerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_valid_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_powerLaw_congr_pred_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_powerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_powerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_variablePowerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_variablePowerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid halfThirdScalingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_valid_from_massPowerLaw_congr_pred

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackagePowerLawBridgeExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) halfThirdScalingCorrelationLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackagePowerLawBridgeExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_from_massPowerLaw_congr_pred


-- created on 2026-10-23
