import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PackageExponentMatchingExample
open StatMech StatMech.Exact3D StatMech.Exact3D.PackageExponentMatchingExample


/--
[halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg_eq :
-- imply
  (halfThirdScalingHyperbolicSplitting.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.halfThirdScalingHyperbolic_ising_predictedExponent_eq_rg

/--
[halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  (halfThirdScalingBlockRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.halfThirdScalingBlockRGPackage_ising_predictedExponent_eq_rg

/--
[halfThirdScalingClosedBall_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma halfThirdScalingClosedBall_ising_predictedExponent_eq_rg_eq :
-- imply
  (halfThirdScalingUnitClosedBallRGPackage.certificate halfThirdScalingBlockScale Ising3DModel).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.halfThirdScalingClosedBall_ising_predictedExponent_eq_rg

/--
[zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  ((zeroTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.zeroTableClosedBallRGPackage_ising_predictedExponent_eq_rg

/--
[generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  ((generatedStableKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.generatedStableKeyReplacedTableClosedBallRGPackage_ising_predictedExponent_eq_rg

/--
[genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  ((genMinCubicKeyReplacedTableClosedBallRGPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.genMinCubicKeyReplacedPackage_ising_predictedExponent_eq_rg

/--
[genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  ((genBoundedCaseReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.genBoundedCaseReplacedPackage_ising_predictedExponent_eq_rg

/--
[genCubicClassReplacedPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma genCubicClassReplacedPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  ((genCubicClassReplacedPackage.retarget Ising3DModel).certificate exampleScale).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.genCubicClassReplacedPackage_ising_predictedExponent_eq_rg

/--
[contributionSplitWitnessPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  ((contributionSplitWitnessPackage.retarget Ising3DModel).certificate).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.contributionSplitWitnessPackage_ising_predictedExponent_eq_rg

/--
[geometricTailWitnessPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  ((geometricTailWitnessPackage.retarget Ising3DModel).certificate).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.geometricTailWitnessPackage_ising_predictedExponent_eq_rg

/--
[zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageExponentMatchingExample.lean)
-/
@[path]
private lemma zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg_eq :
-- imply
  ((zeroTableClosedBallRGPackage.tableWitness.retarget Ising3DModel).certificate).predictedExponent = (halfThirdScalingRGCertificate.retarget Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.PackageExponentMatchingExample.zeroStableKeyTableWitnessPackage_ising_predictedExponent_eq_rg


-- created on 2026-10-23
