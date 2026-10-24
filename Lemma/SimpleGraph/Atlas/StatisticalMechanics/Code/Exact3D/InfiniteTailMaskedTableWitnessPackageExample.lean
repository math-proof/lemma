import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackageExample
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample


/--
[geometricSplit_additive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricSplit_additive_eq :
-- imply
  geometricSplit.Additive := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricSplit_additive

/--
[geometricSplit_total_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricSplit_total_nonneg_eq :
-- imply
  ∀ n : ℕ, 0 ≤ geometricSplit.totalContribution n := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricSplit_total_nonneg

/--
[zeroFiniteTableUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma zeroFiniteTableUpperBound_eq :
-- imply
  FiniteTableUpperBound zeroTable zeroClassifier geometricSplit.finiteContribution 0 where covers := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.zeroFiniteTableUpperBound

/--
[geometricTailEnvelopeOnPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricTailEnvelopeOnPrefix_eq :
-- imply
  geometricSplit.TailEnvelopeOn ({0} : Finset ℕ) InfiniteTailSummabilityExample.geometricHalfTailWeight := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricTailEnvelopeOnPrefix

/--
[geometricPrefixTailEnvelopeSum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricPrefixTailEnvelopeSum_le_one_eq :
-- imply
  (∑ n ∈ ({0} : Finset ℕ), InfiniteTailSummabilityExample.geometricHalfTailWeight n) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricPrefixTailEnvelopeSum_le_one

/--
[geometricSplit_finite_zero_off_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricSplit_finite_zero_off_prefix_eq :
-- imply
  ∀ n : ℕ, n ∉ ({0} : Finset ℕ) → geometricSplit.finiteContribution n = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricSplit_finite_zero_off_prefix

/--
[geometricMaskedTableWitnessPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricMaskedTableWitnessPackage_finiteChecks_eq :
-- imply
  geometricMaskedTableWitnessPackage.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricMaskedTableWitnessPackage_finiteChecks

/--
[geometricMaskedTableWitnessPackage_tailBudget_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricMaskedTableWitnessPackage_tailBudget_eq_one_eq :
-- imply
  geometricMaskedTableWitnessPackage.tailBudget = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricMaskedTableWitnessPackage_tailBudget_eq_one

/--
[geometricMaskedTableWitnessPackage_tableCertifiedTotalBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricMaskedTableWitnessPackage_tableCertifiedTotalBound_eq_two_eq :
-- imply
  geometricMaskedTableWitnessPackage.tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricMaskedTableWitnessPackage_tableCertifiedTotalBound_eq_two

/--
[geometricMaskedTableWitnessPackage_tailTotalTsum_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricMaskedTableWitnessPackage_tailTotalTsum_le_two_eq :
-- imply
  geometricMaskedTableWitnessPackage.tailTotalTsum ≤ 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricMaskedTableWitnessPackage_tailTotalTsum_le_two

/--
[geometricMaskedTableWitnessPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean)
-/
@[path]
private lemma geometricMaskedTableWitnessPackage_valid_of_bridge_eq
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : geometricMaskedTableWitnessPackage.certificate.RGToExponentBridge correlationLength) :
-- imply
  geometricMaskedTableWitnessPackage.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackageExample.geometricMaskedTableWitnessPackage_valid_of_bridge correlationLength hbridge


-- created on 2026-10-23
