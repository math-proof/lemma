import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessPackageExample


/--
[exampleSplit_total_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma exampleSplit_total_nonneg_eq :
-- imply
  ∀ a : Fin 2, 0 ≤ TailSummabilityExample.exampleSplit.totalContribution a := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.exampleSplit_total_nonneg

/--
[contributionSplitWitnessPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_finiteChecks_eq :
-- imply
  contributionSplitWitnessPackage.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_finiteChecks

/--
[contributionSplitWitnessPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_finiteCaseChecks_eq :
-- imply
  contributionSplitWitnessPackage.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_finiteCaseChecks

/--
[contributionSplitWitnessPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_tailBounds_eq :
-- imply
  contributionSplitWitnessPackage.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_tailBounds

/--
[contributionSplitWitnessPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_fixedPointEnclosure_eq :
-- imply
  contributionSplitWitnessPackage.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_fixedPointEnclosure

/--
[contributionSplitWitnessPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_linearizationEnclosure_eq :
-- imply
  contributionSplitWitnessPackage.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_linearizationEnclosure

/--
[contributionSplitWitnessPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hyperbolicSplitting_eq :
-- imply
  contributionSplitWitnessPackage.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_hyperbolicSplitting

/--
[contributionSplitWitnessPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_orbitEntry_eq :
-- imply
  contributionSplitWitnessPackage.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_orbitEntry

/--
[contributionSplitWitnessPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_predictedExponent_eq_eq :
-- imply
  contributionSplitWitnessPackage.certificate.predictedExponent = Real.log exampleScale.toReal / Real.log 3 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_predictedExponent_eq

/--
[contributionSplitWitnessPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : contributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  contributionSplitWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_valid_of_bridge correlationLength hbridge

/--
[contributionSplitWitnessPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : contributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength contributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_hasCriticalNu_of_bridge correlationLength hbridge

/--
[contributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength contributionSplitWitnessPackage.certificate.predictedExponent) :
-- imply
  contributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[contributionSplitWitnessPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel exampleScale 3) correlationLength contributionSplitWitnessPackage.certificate.predictedExponent) :
-- imply
  contributionSplitWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_valid_of_hasCriticalNu correlationLength hν

/--
[hierarchicalStableWitness_fixedPoint_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalStableWitness_fixedPoint_eq_zero_eq :
-- imply
  hierarchicalStableWitness.fixedPoint = (0 : Fin 1 → ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalStableWitness_fixedPoint_eq_zero

/--
[hierarchicalContributionSplitWitnessPackage_fixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_fixedPoint_eq_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.rgMap.map hierarchicalContributionSplitWitnessPackage.fixedPoint = hierarchicalContributionSplitWitnessPackage.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_fixedPoint_eq

/--
[hierarchicalContributionSplitWitnessPackage_stable_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_stable_unique_eq :
-- imply
  ∃! p : Fin 1 → ℝ, hierarchicalStableWitness.map p = p := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_stable_unique

/--
[hierarchicalContributionSplitWitnessPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_finiteChecks_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_finiteChecks

/--
[hierarchicalContributionSplitWitnessPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_finiteCaseChecks_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_finiteCaseChecks

/--
[hierarchicalContributionSplitWitnessPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_tailBounds_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_tailBounds

/--
[hierarchicalContributionSplitWitnessPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_fixedPointEnclosure_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_fixedPointEnclosure

/--
[hierarchicalContributionSplitWitnessPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_linearizationEnclosure_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_linearizationEnclosure

/--
[hierarchicalContributionSplitWitnessPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_hyperbolicSplitting_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_hyperbolicSplitting

/--
[hierarchicalContributionSplitWitnessPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_orbitEntry_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_orbitEntry

/--
[hierarchicalContributionSplitWitnessPackage_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_predictedExponent_eq_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent = Real.log hierarchicalScale.toReal / Real.log hierarchicalThermalEigenvalue := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_predictedExponent_eq

/--
[hierarchicalContributionSplitWitnessPackage_tail_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_tail_bound_eq :
-- imply
  (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤ (∑ a ∈ hierarchicalContributionSplitWitnessPackage.tailCertificate.finitePrefix, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) + hierarchicalContributionSplitWitnessPackage.tailCertificate.tailBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_tail_bound

/--
[contributionSplitWitnessPackage_tail_bound_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_tail_bound_concrete_eq :
-- imply
  (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤ (11 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_tail_bound_concrete

/--
[contributionSplitWitnessPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_tailCertifiedTotalBound_eq_eq :
-- imply
  contributionSplitWitnessPackage.tailCertifiedTotalBound = (11 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_tailCertifiedTotalBound_eq

/--
[contributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound_eq :
-- imply
  (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤ contributionSplitWitnessPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound

/--
[contributionSplitWitnessPackage_tail_tsum_le_three_from_totalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_tail_tsum_le_three_from_totalBound_eq :
-- imply
  (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤ (3 : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_tail_tsum_le_three_from_totalBound

/--
[contributionSplitWitnessPackage_tailTotalTsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_tailTotalTsum_le_certifiedTotalBound_eq :
-- imply
  contributionSplitWitnessPackage.tailTotalTsum ≤ contributionSplitWitnessPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_tailTotalTsum_le_certifiedTotalBound

/--
[contributionSplitWitnessPackage_tailTotalTsum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_tailTotalTsum_split_eq :
-- imply
  contributionSplitWitnessPackage.tailTotalTsum = contributionSplitWitnessPackage.tailPrefixSum + contributionSplitWitnessPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_tailTotalTsum_split

/--
[contributionSplitWitnessPackageRelaxedTailBudget_totalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackageRelaxedTailBudget_totalBound_eq_eq :
-- imply
  contributionSplitWitnessPackageRelaxedTailBudget.tailCertifiedTotalBound = (3 : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackageRelaxedTailBudget_totalBound_eq

/--
[contributionSplitWitnessPackage_tail_tsum_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackage_tail_tsum_le_three_eq :
-- imply
  (∑' a, contributionSplitWitnessPackage.tailCertificate.weight a) ≤ (3 : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackage_tail_tsum_le_three

/--
[contributionSplitWitnessPackageCoarserTailEnvelope_totalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackageCoarserTailEnvelope_totalBound_eq_eq :
-- imply
  contributionSplitWitnessPackageCoarserTailEnvelope.tailCertifiedTotalBound = (3 : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackageCoarserTailEnvelope_totalBound_eq

/--
[contributionSplitWitnessPackageCoarserTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitWitnessPackageCoarserTailEnvelope_certificate_eq_eq :
-- imply
  contributionSplitWitnessPackageCoarserTailEnvelope.certificate = contributionSplitWitnessPackage.certificate := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.contributionSplitWitnessPackageCoarserTailEnvelope_certificate_eq

/--
[hierarchicalContributionSplitWitnessPackage_tail_bound_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_tail_bound_concrete_eq :
-- imply
  (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤ (11 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_tail_bound_concrete

/--
[hierarchicalContributionSplitWitnessPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_eq :
-- imply
  hierarchicalContributionSplitWitnessPackage.tailCertifiedTotalBound = (11 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_tailCertifiedTotalBound_eq

/--
[hierarchicalContributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound_eq :
-- imply
  (∑' a, hierarchicalContributionSplitWitnessPackage.tailCertificate.weight a) ≤ hierarchicalContributionSplitWitnessPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_tail_tsum_le_certifiedTotalBound

/--
[hierarchicalContributionSplitWitnessPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_valid_of_bridge correlationLength hbridge

/--
[hierarchicalContributionSplitWitnessPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu HierarchicalModel correlationLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_hasCriticalNu_of_bridge correlationLength hbridge

/--
[hierarchicalContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu HierarchicalModel correlationLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent) :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[hierarchicalContributionSplitWitnessPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean)
-/
@[path]
private lemma hierarchicalContributionSplitWitnessPackage_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu HierarchicalModel correlationLength hierarchicalContributionSplitWitnessPackage.certificate.predictedExponent) :
-- imply
  hierarchicalContributionSplitWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackageExample.hierarchicalContributionSplitWitnessPackage_valid_of_hasCriticalNu correlationLength hν


-- created on 2026-10-23
