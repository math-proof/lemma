import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample


/--
[generatedBoundedCaseMaskedTablePackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseMaskedTablePackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedBoundedCaseMaskedTablePackage_finiteChecks K support hsaturated

/--
[generatedCubicClassMaskedTablePackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassMaskedTablePackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassMaskedTablePackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedCubicClassMaskedTablePackage_finiteChecks K support hsaturated

/--
[generatedStableKeyMaskedTablePackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyMaskedTablePackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyMaskedTablePackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedStableKeyMaskedTablePackage_finiteChecks K support hsaturated

/--
[generatedMinimalCubicStableKeyMaskedTablePackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyMaskedTablePackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyMaskedTablePackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedMinimalCubicStableKeyMaskedTablePackage_finiteChecks K support hsaturated

/--
[generatedBoundedCaseMaskedTablePackage_budget_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseMaskedTablePackage_budget_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedBoundedCaseMaskedTablePackage_budget_eq_card K support hsaturated

/--
[generatedBoundedCaseMaskedTablePackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseMaskedTablePackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedBoundedCaseMaskedTablePackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedCubicClassMaskedTablePackage_budget_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassMaskedTablePackage_budget_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassMaskedTablePackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedCubicClassMaskedTablePackage_budget_eq_card K support hsaturated

/--
[generatedCubicClassMaskedTablePackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassMaskedTablePackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedCubicClassMaskedTablePackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedStableKeyMaskedTablePackage_budget_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyMaskedTablePackage_budget_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyMaskedTablePackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedStableKeyMaskedTablePackage_budget_eq_card K support hsaturated

/--
[generatedStableKeyMaskedTablePackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyMaskedTablePackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedStableKeyMaskedTablePackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedMinimalCubicStableKeyMaskedTablePackage_budget_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyMaskedTablePackage_budget_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyMaskedTablePackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedMinimalCubicStableKeyMaskedTablePackage_budget_eq_card K support hsaturated

/--
[generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedBoundedCaseMaskedTablePackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseMaskedTablePackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedBoundedCaseMaskedTablePackage_tailRemainderSum_eq_zero K support hsaturated

/--
[generatedBoundedCaseMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum = (generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedBoundedCaseMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[generatedCubicClassMaskedTablePackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassMaskedTablePackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassMaskedTablePackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedCubicClassMaskedTablePackage_tailRemainderSum_eq_zero K support hsaturated

/--
[generatedCubicClassMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum = (generatedCubicClassMaskedTablePackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedCubicClassMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[generatedStableKeyMaskedTablePackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyMaskedTablePackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyMaskedTablePackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedStableKeyMaskedTablePackage_tailRemainderSum_eq_zero K support hsaturated

/--
[generatedStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum = (generatedStableKeyMaskedTablePackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[generatedMinimalCubicStableKeyMaskedTablePackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyMaskedTablePackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyMaskedTablePackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedMinimalCubicStableKeyMaskedTablePackage_tailRemainderSum_eq_zero K support hsaturated

/--
[generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum = (generatedMinimalCubicStableKeyMaskedTablePackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedMinimalCubicStableKeyMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_budget_eq K support hsaturated

/--
[generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (generatedBoundedCaseMaskedTablePackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_tsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_tsum_le_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedBoundedCaseMaskedTablePackage_replacedTailEnvelope_tsum_le K support hsaturated

/--
[generatedCubicClassMaskedTablePackage_replacedTailEnvelope_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassMaskedTablePackage_replacedTailEnvelope_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedCubicClassMaskedTablePackage_replacedTailEnvelope_budget_eq K support hsaturated

/--
[generatedCubicClassMaskedTablePackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassMaskedTablePackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (generatedCubicClassMaskedTablePackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedCubicClassMaskedTablePackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[generatedCubicClassMaskedTablePackage_replacedTailEnvelope_tsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassMaskedTablePackage_replacedTailEnvelope_tsum_le_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedCubicClassMaskedTablePackage_replacedTailEnvelope_tsum_le K support hsaturated

/--
[generatedStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq K support hsaturated

/--
[generatedStableKeyMaskedTablePackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyMaskedTablePackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (generatedStableKeyMaskedTablePackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedStableKeyMaskedTablePackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[generatedStableKeyMaskedTablePackage_replacedTailEnvelope_tsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyMaskedTablePackage_replacedTailEnvelope_tsum_le_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedStableKeyMaskedTablePackage_replacedTailEnvelope_tsum_le K support hsaturated

/--
[generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_budget_eq K support hsaturated

/--
[generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (generatedMinimalCubicStableKeyMaskedTablePackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_tsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_tsum_le_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedGeneratedTablePackageExample.generatedMinimalCubicStableKeyMaskedTablePackage_replacedTailEnvelope_tsum_le K support hsaturated


-- created on 2026-10-23
