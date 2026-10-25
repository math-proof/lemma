import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part7
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailWitnessPackageExample


/--
[geometricTailWitnessPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_finiteChecks_eq :
-- imply
  geometricTailWitnessPackage.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_finiteChecks

/--
[geometricTailWitnessPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_finiteCaseChecks_eq :
-- imply
  geometricTailWitnessPackage.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_finiteCaseChecks

/--
[geometricTailWitnessPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailBounds_eq :
-- imply
  geometricTailWitnessPackage.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailBounds

/--
[geometricTailWitnessPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_fixedPointEnclosure_eq :
-- imply
  geometricTailWitnessPackage.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_fixedPointEnclosure

/--
[geometricTailWitnessPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_linearizationEnclosure_eq :
-- imply
  geometricTailWitnessPackage.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_linearizationEnclosure

/--
[geometricTailWitnessPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hyperbolicSplitting_eq :
-- imply
  geometricTailWitnessPackage.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_hyperbolicSplitting

/--
[geometricTailWitnessPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_orbitEntry_eq :
-- imply
  geometricTailWitnessPackage.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_orbitEntry

/--
[geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one_eq :
-- imply
  geometricTailWitnessPackage.tailCertifiedTotalBound = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailCertifiedTotalBound_eq_one

/--
[geometricTailWitnessPackage_tail_tsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tail_tsum_le_one_eq :
-- imply
  (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tail_tsum_le_one

/--
[geometricTailWitnessPackage_tail_tsum_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tail_tsum_le_two_eq :
-- imply
  (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) ≤ 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tail_tsum_le_two

/--
[geometricTailWitnessPackage_tailTotalTsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailTotalTsum_le_one_eq :
-- imply
  geometricTailWitnessPackage.tailTotalTsum ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailTotalTsum_le_one

/--
[geometricTailWitnessPackage_tailTotalTsum_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailTotalTsum_le_two_eq :
-- imply
  geometricTailWitnessPackage.tailTotalTsum ≤ 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailTotalTsum_le_two

/--
[geometricTailWitnessPackage_tailTotalTsum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailTotalTsum_split_eq :
-- imply
  geometricTailWitnessPackage.tailTotalTsum = geometricTailWitnessPackage.tailPrefixSum + geometricTailWitnessPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailTotalTsum_split

/--
[geometricTailWitnessPackage_tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailTotalTsum_eq_tsum_eq :
-- imply
  geometricTailWitnessPackage.tailTotalTsum = (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailTotalTsum_eq_tsum

/--
[geometricTailWitnessPackage_summable_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_summable_tailContribution_eq :
-- imply
  Summable geometricTailWitnessPackage.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_summable_tailContribution

/--
[geometricTailWitnessPackage_tailContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailContribution_nonneg_eq
  {n : ℕ} :
-- imply
  0 ≤ geometricTailWitnessPackage.tailContribution n := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailContribution_nonneg n

/--
[geometricTailWitnessPackage_tailPrefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailPrefixSum_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackage.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailPrefixSum_nonneg

/--
[geometricTailWitnessPackage_tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailBudget_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailBudget_nonneg

/--
[geometricTailWitnessPackage_tailCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailCertifiedTotalBound_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailCertifiedTotalBound_nonneg

/--
[geometricTailWitnessPackage_tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tail_tsum_nonneg_eq :
-- imply
  0 ≤ (∑' n : ℕ, geometricTailWitnessPackage.tailCertificate.weight n) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tail_tsum_nonneg

/--
[geometricTailWitnessPackage_tailTotalTsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailTotalTsum_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackage.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailTotalTsum_nonneg

/--
[geometricTailWitnessPackage_tailRemainderSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailRemainderSum_le_tailBudget_eq :
-- imply
  geometricTailWitnessPackage.tailRemainderSum ≤ geometricTailWitnessPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailRemainderSum_le_tailBudget

/--
[geometricTailWitnessPackage_tailRemainderSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_tailRemainderSum_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_tailRemainderSum_nonneg

/--
[geometricTailWitnessPackage_stable_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_stable_fixedPoint_mem_eq :
-- imply
  FiniteContraction.ClosedBall geometricTailWitnessPackage.stable.contraction.center geometricTailWitnessPackage.stable.contraction.radius geometricTailWitnessPackage.stable.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_stable_fixedPoint_mem

/--
[geometricTailWitnessPackage_stable_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_stable_exists_unique_fixedPoint_eq :
-- imply
  ∃! p : Fin geometricTailWitnessPackage.nStable → ℝ, geometricTailWitnessPackage.stable.map p = p := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_stable_exists_unique_fixedPoint

/--
[geometricTailWitnessPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricTailWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  geometricTailWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_valid_of_bridge correlationLength hbridge

/--
[geometricTailWitnessPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricTailWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricTailWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_hasCriticalNu_of_bridge correlationLength hbridge

/--
[geometricTailWitnessPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricTailWitnessPackage.certificate.predictedExponent) :
-- imply
  geometricTailWitnessPackage.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[geometricTailWitnessPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackage_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricTailWitnessPackage.certificate.predictedExponent) :
-- imply
  geometricTailWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackage_valid_of_hasCriticalNu correlationLength hν

/--
[geometricTailWitnessPackageFromEnvelope_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_finiteChecks_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_finiteChecks

/--
[geometricTailWitnessPackageFromEnvelope_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_finiteCaseChecks_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_finiteCaseChecks

/--
[geometricTailWitnessPackageFromEnvelope_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailBounds_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailBounds

/--
[geometricTailWitnessPackageFromEnvelope_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_fixedPointEnclosure_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_fixedPointEnclosure

/--
[geometricTailWitnessPackageFromEnvelope_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_linearizationEnclosure_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_linearizationEnclosure

/--
[geometricTailWitnessPackageFromEnvelope_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_hyperbolicSplitting_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_hyperbolicSplitting

/--
[geometricTailWitnessPackageFromEnvelope_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_orbitEntry_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_orbitEntry

/--
[geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.tailCertifiedTotalBound = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_eq_one

/--
[geometricTailWitnessPackageFromEnvelope_tail_tsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tail_tsum_le_one_eq :
-- imply
  (∑' n : ℕ, geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tail_tsum_le_one

/--
[geometricTailWitnessPackageFromEnvelope_tailTotalTsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailTotalTsum_le_one_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailTotalTsum_le_one

/--
[geometricTailWitnessPackageFromEnvelope_tailTotalTsum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailTotalTsum_split_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum = geometricTailWitnessPackageFromEnvelope.tailPrefixSum + geometricTailWitnessPackageFromEnvelope.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailTotalTsum_split

/--
[geometricTailWitnessPackageFromEnvelope_tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailTotalTsum_eq_tsum_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.tailTotalTsum = (∑' n : ℕ, geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailTotalTsum_eq_tsum

/--
[geometricTailWitnessPackageFromEnvelope_summable_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_summable_tailContribution_eq :
-- imply
  Summable geometricTailWitnessPackageFromEnvelope.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_summable_tailContribution

/--
[geometricTailWitnessPackageFromEnvelope_tailContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailContribution_nonneg_eq
  {n : ℕ} :
-- imply
  0 ≤ geometricTailWitnessPackageFromEnvelope.tailContribution n := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailContribution_nonneg n

/--
[geometricTailWitnessPackageFromEnvelope_tailPrefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailPrefixSum_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackageFromEnvelope.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailPrefixSum_nonneg

/--
[geometricTailWitnessPackageFromEnvelope_tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailBudget_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackageFromEnvelope.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailBudget_nonneg

/--
[geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackageFromEnvelope.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailCertifiedTotalBound_nonneg

/--
[geometricTailWitnessPackageFromEnvelope_tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tail_tsum_nonneg_eq :
-- imply
  0 ≤ (∑' n : ℕ, geometricTailWitnessPackageFromEnvelope.tailCertificate.weight n) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tail_tsum_nonneg

/--
[geometricTailWitnessPackageFromEnvelope_tailTotalTsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailTotalTsum_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackageFromEnvelope.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailTotalTsum_nonneg

/--
[geometricTailWitnessPackageFromEnvelope_tailRemainderSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailRemainderSum_le_tailBudget_eq :
-- imply
  geometricTailWitnessPackageFromEnvelope.tailRemainderSum ≤ geometricTailWitnessPackageFromEnvelope.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailRemainderSum_le_tailBudget

/--
[geometricTailWitnessPackageFromEnvelope_tailRemainderSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_tailRemainderSum_nonneg_eq :
-- imply
  0 ≤ geometricTailWitnessPackageFromEnvelope.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_tailRemainderSum_nonneg

/--
[geometricTailWitnessPackageFromEnvelope_stable_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_stable_fixedPoint_mem_eq :
-- imply
  FiniteContraction.ClosedBall geometricTailWitnessPackageFromEnvelope.stable.contraction.center geometricTailWitnessPackageFromEnvelope.stable.contraction.radius geometricTailWitnessPackageFromEnvelope.stable.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_stable_fixedPoint_mem

/--
[geometricTailWitnessPackageFromEnvelope_stable_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_stable_exists_unique_fixedPoint_eq :
-- imply
  ∃! p : Fin geometricTailWitnessPackageFromEnvelope.nStable → ℝ, geometricTailWitnessPackageFromEnvelope.stable.map p = p := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_stable_exists_unique_fixedPoint

/--
[geometricTailWitnessPackageFromEnvelope_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge correlationLength) :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_valid_of_bridge correlationLength hbridge

/--
[geometricTailWitnessPackageFromEnvelope_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_hasCriticalNu_of_bridge correlationLength hbridge

/--
[geometricTailWitnessPackageFromEnvelope_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent) :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[geometricTailWitnessPackageFromEnvelope_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromEnvelope_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricTailWitnessPackageFromEnvelope.certificate.predictedExponent) :
-- imply
  geometricTailWitnessPackageFromEnvelope.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromEnvelope_valid_of_hasCriticalNu correlationLength hν

/--
[geometricTailWitnessPackageFromMaskedEnvelope_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromMaskedEnvelope_finiteChecks_eq :
-- imply
  geometricTailWitnessPackageFromMaskedEnvelope.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromMaskedEnvelope_finiteChecks

/--
[geometricTailWitnessPackageFromMaskedEnvelope_tailBudget_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromMaskedEnvelope_tailBudget_eq_one_eq :
-- imply
  geometricTailWitnessPackageFromMaskedEnvelope.tailBudget = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromMaskedEnvelope_tailBudget_eq_one

/--
[geometricTailWitnessPackageFromMaskedEnvelope_tailTotalTsum_le_prefix_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailWitnessPackageFromMaskedEnvelope_tailTotalTsum_le_prefix_add_one_eq :
-- imply
  geometricTailWitnessPackageFromMaskedEnvelope.tailTotalTsum ≤ geometricTailWitnessPackageFromMaskedEnvelope.tailPrefixSum + 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricTailWitnessPackageFromMaskedEnvelope_tailTotalTsum_le_prefix_add_one

/--
[geometricContributionSplitMaskedTailEnvelopeWitnessPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitMaskedTailEnvelopeWitnessPackage_finiteChecks_eq :
-- imply
  RGCertificate.FiniteChecks geometricContributionSplitMaskedTailEnvelopeWitnessPackage.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitMaskedTailEnvelopeWitnessPackage_finiteChecks

/--
[geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailBudget_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailBudget_eq_one_eq :
-- imply
  geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailBudget = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailBudget_eq_one

/--
[geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailTotalTsum_le_prefix_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailTotalTsum_le_prefix_add_one_eq :
-- imply
  geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailTotalTsum ≤ geometricContributionSplitMaskedTailEnvelopeWitnessPackage.tailPrefixSum + 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitMaskedTailEnvelopeWitnessPackage_tailTotalTsum_le_prefix_add_one

/--
[geometricContributionSplitWitnessPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_finiteChecks_eq :
-- imply
  geometricContributionSplitWitnessPackage.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_finiteChecks

/--
[geometricContributionSplitWitnessPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_finiteCaseChecks_eq :
-- imply
  geometricContributionSplitWitnessPackage.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_finiteCaseChecks

/--
[geometricContributionSplitWitnessPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailBounds_eq :
-- imply
  geometricContributionSplitWitnessPackage.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailBounds

/--
[geometricContributionSplitWitnessPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_fixedPointEnclosure_eq :
-- imply
  geometricContributionSplitWitnessPackage.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_fixedPointEnclosure

/--
[geometricContributionSplitWitnessPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_linearizationEnclosure_eq :
-- imply
  geometricContributionSplitWitnessPackage.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_linearizationEnclosure

/--
[geometricContributionSplitWitnessPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_hyperbolicSplitting_eq :
-- imply
  geometricContributionSplitWitnessPackage.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_hyperbolicSplitting

/--
[geometricContributionSplitWitnessPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_orbitEntry_eq :
-- imply
  geometricContributionSplitWitnessPackage.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_orbitEntry

/--
[geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one_eq :
-- imply
  geometricContributionSplitWitnessPackage.tailCertifiedTotalBound = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_eq_one

/--
[geometricContributionSplitWitnessPackage_tail_tsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tail_tsum_le_one_eq :
-- imply
  (∑' n : ℕ, geometricContributionSplitWitnessPackage.tailCertificate.weight n) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tail_tsum_le_one

/--
[geometricContributionSplitWitnessPackage_tailTotalTsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailTotalTsum_le_one_eq :
-- imply
  geometricContributionSplitWitnessPackage.tailTotalTsum ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailTotalTsum_le_one

/--
[geometricContributionSplitWitnessPackage_tailTotalTsum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailTotalTsum_split_eq :
-- imply
  geometricContributionSplitWitnessPackage.tailTotalTsum = geometricContributionSplitWitnessPackage.tailPrefixSum + geometricContributionSplitWitnessPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailTotalTsum_split

/--
[geometricContributionSplitWitnessPackage_tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailTotalTsum_eq_tsum_eq :
-- imply
  geometricContributionSplitWitnessPackage.tailTotalTsum = (∑' n : ℕ, geometricContributionSplitWitnessPackage.tailCertificate.weight n) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailTotalTsum_eq_tsum

/--
[geometricContributionSplitWitnessPackage_summable_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_summable_tailContribution_eq :
-- imply
  Summable geometricContributionSplitWitnessPackage.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_summable_tailContribution

/--
[geometricContributionSplitWitnessPackage_tailContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailContribution_nonneg_eq
  {n : ℕ} :
-- imply
  0 ≤ geometricContributionSplitWitnessPackage.tailContribution n := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailContribution_nonneg n

/--
[geometricContributionSplitWitnessPackage_tailPrefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailPrefixSum_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitWitnessPackage.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailPrefixSum_nonneg

/--
[geometricContributionSplitWitnessPackage_tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailBudget_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitWitnessPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailBudget_nonneg

/--
[geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitWitnessPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailCertifiedTotalBound_nonneg

/--
[geometricContributionSplitWitnessPackage_tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tail_tsum_nonneg_eq :
-- imply
  0 ≤ (∑' n : ℕ, geometricContributionSplitWitnessPackage.tailCertificate.weight n) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tail_tsum_nonneg

/--
[geometricContributionSplitWitnessPackage_tailTotalTsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailTotalTsum_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitWitnessPackage.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailTotalTsum_nonneg

/--
[geometricContributionSplitWitnessPackage_tailRemainderSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailRemainderSum_le_tailBudget_eq :
-- imply
  geometricContributionSplitWitnessPackage.tailRemainderSum ≤ geometricContributionSplitWitnessPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailRemainderSum_le_tailBudget

/--
[geometricContributionSplitWitnessPackage_tailRemainderSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_tailRemainderSum_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitWitnessPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_tailRemainderSum_nonneg

/--
[geometricContributionSplitWitnessPackage_stable_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_stable_fixedPoint_mem_eq :
-- imply
  FiniteContraction.ClosedBall geometricContributionSplitWitnessPackage.stable.contraction.center geometricContributionSplitWitnessPackage.stable.contraction.radius geometricContributionSplitWitnessPackage.stable.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_stable_fixedPoint_mem

/--
[geometricContributionSplitWitnessPackage_stable_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_stable_exists_unique_fixedPoint_eq :
-- imply
  ∃! p : Fin geometricContributionSplitWitnessPackage.nStable → ℝ, geometricContributionSplitWitnessPackage.stable.map p = p := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_stable_exists_unique_fixedPoint

/--
[geometricContributionSplitWitnessPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  geometricContributionSplitWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_valid_of_bridge correlationLength hbridge

/--
[geometricContributionSplitWitnessPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricContributionSplitWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_hasCriticalNu_of_bridge correlationLength hbridge

/--
[geometricContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricContributionSplitWitnessPackage.certificate.predictedExponent) :
-- imply
  geometricContributionSplitWitnessPackage.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[geometricContributionSplitWitnessPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitWitnessPackage_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricContributionSplitWitnessPackage.certificate.predictedExponent) :
-- imply
  geometricContributionSplitWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitWitnessPackage_valid_of_hasCriticalNu correlationLength hν

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_finiteChecks_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_finiteChecks

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_finiteCaseChecks_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_finiteCaseChecks

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailBounds_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailBounds

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_fixedPointEnclosure_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_fixedPointEnclosure

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_linearizationEnclosure_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_linearizationEnclosure

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_hyperbolicSplitting_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_hyperbolicSplitting

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_orbitEntry_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_orbitEntry

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.tailCertifiedTotalBound = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_eq_one

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_le_one_eq :
-- imply
  (∑' n : ℕ, geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight n) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_le_one

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_le_one_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_le_one

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_split_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum = geometricContributionSplitTailEnvelopeWitnessPackage.tailPrefixSum + geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_split

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_eq_tsum_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum = (∑' n : ℕ, geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight n) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_eq_tsum

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_summable_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_summable_tailContribution_eq :
-- imply
  Summable geometricContributionSplitTailEnvelopeWitnessPackage.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_summable_tailContribution

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailContribution_nonneg_eq
  {n : ℕ} :
-- imply
  0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailContribution n := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailContribution_nonneg n

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailPrefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailPrefixSum_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailPrefixSum_nonneg

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailBudget_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailBudget_nonneg

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailCertifiedTotalBound_nonneg

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_nonneg_eq :
-- imply
  0 ≤ (∑' n : ℕ, geometricContributionSplitTailEnvelopeWitnessPackage.tailCertificate.weight n) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tail_tsum_nonneg

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailTotalTsum_nonneg

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_le_tailBudget_eq :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_le_tailBudget

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_nonneg_eq :
-- imply
  0 ≤ geometricContributionSplitTailEnvelopeWitnessPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_tailRemainderSum_nonneg

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_stable_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_stable_fixedPoint_mem_eq :
-- imply
  FiniteContraction.ClosedBall geometricContributionSplitTailEnvelopeWitnessPackage.stable.contraction.center geometricContributionSplitTailEnvelopeWitnessPackage.stable.contraction.radius geometricContributionSplitTailEnvelopeWitnessPackage.stable.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_stable_fixedPoint_mem

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_stable_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_stable_exists_unique_fixedPoint_eq :
-- imply
  ∃! p : Fin geometricContributionSplitTailEnvelopeWitnessPackage.nStable → ℝ, geometricContributionSplitTailEnvelopeWitnessPackage.stable.map p = p := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_stable_exists_unique_fixedPoint

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_bridge correlationLength hbridge

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_hasCriticalNu_of_bridge correlationLength hbridge

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent) :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength geometricContributionSplitTailEnvelopeWitnessPackage.certificate.predictedExponent) :
-- imply
  geometricContributionSplitTailEnvelopeWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.geometricContributionSplitTailEnvelopeWitnessPackage_valid_of_hasCriticalNu correlationLength hν

/--
[contributionSplitAsInfiniteTailPackage_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_certificate_eq_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate = FiniteWitnessPackageExample.contributionSplitWitnessPackage.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_certificate_eq

/--
[contributionSplitAsInfiniteTailPackage_tailPrefixSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailPrefixSum_eq_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailPrefixSum = FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailPrefixSum_eq

/--
[contributionSplitAsInfiniteTailPackage_tailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailBudget_eq_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailBudget = FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailBudget_eq

/--
[contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq_finite_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound = FiniteWitnessPackageExample.contributionSplitWitnessPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq_finite

/--
[contributionSplitAsInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_finiteChecks_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_finiteChecks

/--
[contributionSplitAsInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_finiteCaseChecks_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_finiteCaseChecks

/--
[contributionSplitAsInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailBounds_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailBounds

/--
[contributionSplitAsInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_fixedPointEnclosure_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_fixedPointEnclosure

/--
[contributionSplitAsInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_linearizationEnclosure_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_linearizationEnclosure

/--
[contributionSplitAsInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_hyperbolicSplitting_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_hyperbolicSplitting

/--
[contributionSplitAsInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_orbitEntry_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_orbitEntry

/--
[contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound = (11 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_eq

/--
[contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_certified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_certified_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailTotalTsum ≤ contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_certified

/--
[contributionSplitAsInfiniteTailPackage_tail_tsum_le_11_div_5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tail_tsum_le_11_div_5_eq :
-- imply
  (∑' a : Fin 2, contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) ≤ (11 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tail_tsum_le_11_div_5

/--
[contributionSplitAsInfiniteTailPackage_tail_tsum_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tail_tsum_le_three_eq :
-- imply
  (∑' a : Fin 2, contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) ≤ (3 : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tail_tsum_le_three

/--
[contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_11_div_5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_11_div_5_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailTotalTsum ≤ (11 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailTotalTsum_le_11_div_5

/--
[contributionSplitAsInfiniteTailPackage_tailTotalTsum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailTotalTsum_split_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailTotalTsum = contributionSplitAsInfiniteTailPackage.tailPrefixSum + contributionSplitAsInfiniteTailPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailTotalTsum_split

/--
[contributionSplitAsInfiniteTailPackage_tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailTotalTsum_eq_tsum_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailTotalTsum = (∑' a : Fin 2, contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailTotalTsum_eq_tsum

/--
[contributionSplitAsInfiniteTailPackage_summable_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_summable_tailContribution_eq :
-- imply
  Summable contributionSplitAsInfiniteTailPackage.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_summable_tailContribution

/--
[contributionSplitAsInfiniteTailPackage_tailContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailContribution_nonneg_eq
  {a : Fin 2} :
-- imply
  0 ≤ contributionSplitAsInfiniteTailPackage.tailContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailContribution_nonneg a

/--
[contributionSplitAsInfiniteTailPackage_tailPrefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailPrefixSum_nonneg_eq :
-- imply
  0 ≤ contributionSplitAsInfiniteTailPackage.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailPrefixSum_nonneg

/--
[contributionSplitAsInfiniteTailPackage_tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailBudget_nonneg_eq :
-- imply
  0 ≤ contributionSplitAsInfiniteTailPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailBudget_nonneg

/--
[contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_nonneg_eq :
-- imply
  0 ≤ contributionSplitAsInfiniteTailPackage.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailCertifiedTotalBound_nonneg

/--
[contributionSplitAsInfiniteTailPackage_tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tail_tsum_nonneg_eq :
-- imply
  0 ≤ (∑' a : Fin 2, contributionSplitAsInfiniteTailPackage.tailCertificate.weight a) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tail_tsum_nonneg

/--
[contributionSplitAsInfiniteTailPackage_tailTotalTsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailTotalTsum_nonneg_eq :
-- imply
  0 ≤ contributionSplitAsInfiniteTailPackage.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailTotalTsum_nonneg

/--
[contributionSplitAsInfiniteTailPackage_tailRemainderSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailRemainderSum_le_tailBudget_eq :
-- imply
  contributionSplitAsInfiniteTailPackage.tailRemainderSum ≤ contributionSplitAsInfiniteTailPackage.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailRemainderSum_le_tailBudget

/--
[contributionSplitAsInfiniteTailPackage_tailRemainderSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_tailRemainderSum_nonneg_eq :
-- imply
  0 ≤ contributionSplitAsInfiniteTailPackage.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_tailRemainderSum_nonneg

/--
[contributionSplitAsInfiniteTailPackage_stable_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_stable_fixedPoint_mem_eq :
-- imply
  FiniteContraction.ClosedBall contributionSplitAsInfiniteTailPackage.stable.contraction.center contributionSplitAsInfiniteTailPackage.stable.contraction.radius contributionSplitAsInfiniteTailPackage.stable.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_stable_fixedPoint_mem

/--
[contributionSplitAsInfiniteTailPackage_stable_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_stable_exists_unique_fixedPoint_eq :
-- imply
  ∃! p : Fin contributionSplitAsInfiniteTailPackage.nStable → ℝ, contributionSplitAsInfiniteTailPackage.stable.map p = p := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_stable_exists_unique_fixedPoint

/--
[contributionSplitAsInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_valid_of_bridge correlationLength hbridge

/--
[contributionSplitAsInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength contributionSplitAsInfiniteTailPackage.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_hasCriticalNu_of_bridge correlationLength hbridge

/--
[contributionSplitAsInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength contributionSplitAsInfiniteTailPackage.certificate.predictedExponent) :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu correlationLength hν

/--
[contributionSplitAsInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean)
-/
@[path]
private lemma contributionSplitAsInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength contributionSplitAsInfiniteTailPackage.certificate.predictedExponent) :
-- imply
  contributionSplitAsInfiniteTailPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackageExample.contributionSplitAsInfiniteTailPackage_valid_of_hasCriticalNu correlationLength hν


-- created on 2026-10-23
