import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PackageReparameterizationComparisonExample.Part3
open StatMech StatMech.Exact3D StatMech.Exact3D.PackageReparameterizationComparisonExample


/--
[halfThirdScalingReparameterizedLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma halfThirdScalingReparameterizedLength_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), 0 < halfThirdScalingReparameterizedLength β := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.halfThirdScalingReparameterizedLength_pos

/--
[halfThirdScalingDoubledReparameterizedLength_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma halfThirdScalingDoubledReparameterizedLength_comparable_eq :
-- imply
  ∀ᶠ β in nhdsWithin halfThirdScalingModel.betaC (Set.Iio halfThirdScalingModel.betaC), (2 : ℝ) * halfThirdScalingReparameterizedLength β ≤ halfThirdScalingDoubledReparameterizedLength β ∧ halfThirdScalingDoubledReparameterizedLength β ≤ (2 : ℝ) * halfThirdScalingReparameterizedLength β := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.halfThirdScalingDoubledReparameterizedLength_comparable

/--
[halfThirdScalingHyperbolicSplitting_bridge_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_bridge_doubled_reparameterized_eq :
-- imply
  halfThirdScalingRGCertificate.RGToExponentBridge halfThirdScalingDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.halfThirdScalingHyperbolicSplitting_bridge_doubled_reparameterized

/--
[halfThirdScalingHyperbolicSplitting_valid_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_valid_doubled_reparameterized_eq :
-- imply
  halfThirdScalingRGCertificate.Valid halfThirdScalingDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.halfThirdScalingHyperbolicSplitting_valid_doubled_reparameterized

/--
[halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_reparameterized_eq :
-- imply
  HasCriticalNu halfThirdScalingModel halfThirdScalingDoubledReparameterizedLength halfThirdScalingRGCertificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.halfThirdScalingHyperbolicSplitting_hasCriticalNu_doubled_reparameterized

/--
[zeroTableClosedBallReparameterizedLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma zeroTableClosedBallReparameterizedLength_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), 0 < zeroTableClosedBallReparameterizedLength β := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.zeroTableClosedBallReparameterizedLength_pos

/--
[zeroTableClosedBallDoubledReparameterizedLength_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma zeroTableClosedBallDoubledReparameterizedLength_comparable_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), (2 : ℝ) * zeroTableClosedBallReparameterizedLength β ≤ zeroTableClosedBallDoubledReparameterizedLength β ∧ zeroTableClosedBallDoubledReparameterizedLength β ≤ (2 : ℝ) * zeroTableClosedBallReparameterizedLength β := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.zeroTableClosedBallDoubledReparameterizedLength_comparable

/--
[zeroTableClosedBallRGPackage_bridge_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_bridge_doubled_reparameterized_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge zeroTableClosedBallDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.zeroTableClosedBallRGPackage_bridge_doubled_reparameterized

/--
[zeroTableClosedBallRGPackage_valid_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_valid_doubled_reparameterized_eq :
-- imply
  (zeroTableClosedBallRGPackage.certificate exampleScale).Valid zeroTableClosedBallDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.zeroTableClosedBallRGPackage_valid_doubled_reparameterized

/--
[zeroTableClosedBallRGPackage_hasCriticalNu_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_hasCriticalNu_doubled_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) zeroTableClosedBallDoubledReparameterizedLength (zeroTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.zeroTableClosedBallRGPackage_hasCriticalNu_doubled_reparameterized

/--
[generatedReplacedReparameterizedLength_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma generatedReplacedReparameterizedLength_pos_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), 0 < zeroTableClosedBallReparameterizedLength β := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.generatedReplacedReparameterizedLength_pos

/--
[generatedReplacedDoubledReparameterizedLength_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma generatedReplacedDoubledReparameterizedLength_comparable_eq :
-- imply
  ∀ᶠ β in nhdsWithin (ToyCriticalModel exampleScale 3).betaC (Set.Iio (ToyCriticalModel exampleScale 3).betaC), (2 : ℝ) * zeroTableClosedBallReparameterizedLength β ≤ generatedReplacedDoubledReparameterizedLength β ∧ generatedReplacedDoubledReparameterizedLength β ≤ (2 : ℝ) * zeroTableClosedBallReparameterizedLength β := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.generatedReplacedDoubledReparameterizedLength_comparable

/--
[generatedReplacedTCBRGPackage_bridge_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_bridge_doubled_reparameterized_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge generatedReplacedDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.generatedReplacedTCBRGPackage_bridge_doubled_reparameterized

/--
[generatedReplacedTCBRGPackage_valid_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_valid_doubled_reparameterized_eq :
-- imply
  (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid generatedReplacedDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.generatedReplacedTCBRGPackage_valid_doubled_reparameterized

/--
[generatedReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma generatedReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) generatedReplacedDoubledReparameterizedLength (generatedStableKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.generatedReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized

/--
[genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_reparameterized_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).RGToExponentBridge generatedReplacedDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genMinCubicKeyReplacedTCBRGPackage_bridge_doubled_reparameterized

/--
[genMinCubicKeyReplacedTCBRGPackage_valid_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_valid_doubled_reparameterized_eq :
-- imply
  (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).Valid generatedReplacedDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genMinCubicKeyReplacedTCBRGPackage_valid_doubled_reparameterized

/--
[genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) generatedReplacedDoubledReparameterizedLength (genMinCubicKeyReplacedTableClosedBallRGPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genMinCubicKeyReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized

/--
[genBoundedCaseReplacedTCBRGPackage_bridge_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_bridge_doubled_reparameterized_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).RGToExponentBridge generatedReplacedDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genBoundedCaseReplacedTCBRGPackage_bridge_doubled_reparameterized

/--
[genBoundedCaseReplacedTCBRGPackage_valid_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_valid_doubled_reparameterized_eq :
-- imply
  (genBoundedCaseReplacedPackage.certificate exampleScale).Valid generatedReplacedDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genBoundedCaseReplacedTCBRGPackage_valid_doubled_reparameterized

/--
[genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) generatedReplacedDoubledReparameterizedLength (genBoundedCaseReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genBoundedCaseReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized

/--
[genCubicClassReplacedTCBRGPackage_bridge_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_bridge_doubled_reparameterized_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).RGToExponentBridge generatedReplacedDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genCubicClassReplacedTCBRGPackage_bridge_doubled_reparameterized

/--
[genCubicClassReplacedTCBRGPackage_valid_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_valid_doubled_reparameterized_eq :
-- imply
  (genCubicClassReplacedPackage.certificate exampleScale).Valid generatedReplacedDoubledReparameterizedLength := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genCubicClassReplacedTCBRGPackage_valid_doubled_reparameterized

/--
[genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageReparameterizationComparisonExample.lean)
-/
@[path]
private lemma genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized_eq :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) generatedReplacedDoubledReparameterizedLength (genCubicClassReplacedPackage.certificate exampleScale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageReparameterizationComparisonExample.genCubicClassReplacedTCBRGPackage_hasCriticalNu_doubled_reparameterized


-- created on 2026-10-23
