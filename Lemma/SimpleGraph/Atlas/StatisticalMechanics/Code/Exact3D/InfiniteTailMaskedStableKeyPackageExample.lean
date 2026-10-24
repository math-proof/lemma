import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedStableKeyPackageExample
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample


/--
[rawRowsZeroMaskedTablePackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroMaskedTablePackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroMaskedTablePackage (d := d) K).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawRowsZeroMaskedTablePackage_finiteChecks K

/--
[minimalCubicRowsZeroMaskedTablePackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroMaskedTablePackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroMaskedTablePackage (d := d) K).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicRowsZeroMaskedTablePackage_finiteChecks K

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_finiteChecks K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_finiteChecks K support hsaturated

/--
[rawRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroMaskedTablePackage (d := d) K).tableCertifiedTotalBound = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero K

/--
[minimalCubicRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroMaskedTablePackage (d := d) K).tableCertifiedTotalBound = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicRowsZeroMaskedTablePackage_tableCertifiedTotalBound_eq_zero K

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_budget_eq_card K support hsaturated

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  ((rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [rawZeroOneRowsIndicatorMaskedTablePackage, ofExternalStableKeyRowsFiniteCutoffStableKey])).finiteBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two K support hsaturated

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  ((rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [rawZeroOneRowsIndicatorMaskedTablePackage, ofExternalStableKeyRowsFiniteCutoffStableKey] )).tableCertifiedTotalBound = (support.card : ℝ) * 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage, ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).finiteBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_eq_two K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage, ofExternalStableKeyRowsFiniteCutoffMinimalCubic] )).tableCertifiedTotalBound = (support.card : ℝ) * 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedFiniteBound_budget_eq K support hsaturated

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  ((rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).with_larger_prefixTailBound (prefixTailBound' := 1) (by norm_num [rawZeroOneRowsIndicatorMaskedTablePackage, ofExternalStableKeyRowsFiniteCutoffStableKey] )).tableCertifiedTotalBound = (support.card : ℝ) + 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).with_larger_prefixTailBound (prefixTailBound' := 1) (by norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage, ofExternalStableKeyRowsFiniteCutoffMinimalCubic] )).tableCertifiedTotalBound = (support.card : ℝ) + 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedPrefixBudget_eq K support hsaturated

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  ((rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).with_larger_tailBound (tailBound' := 1) (by norm_num [rawZeroOneRowsIndicatorMaskedTablePackage, ofExternalStableKeyRowsFiniteCutoffStableKey] )).tableCertifiedTotalBound = (support.card : ℝ) + 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  ((minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).with_larger_tailBound (tailBound' := 1) (by norm_num [minimalCubicZeroOneRowsIndicatorMaskedTablePackage, ofExternalStableKeyRowsFiniteCutoffMinimalCubic] )).tableCertifiedTotalBound = (support.card : ℝ) + 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_relaxedTailBudget_eq K support hsaturated

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq K support hsaturated

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_budget_eq K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_replacedTailEnvelope_tsum_le K support hsaturated

/--
[rawRowsZeroMaskedTablePackage_tailTotalTsum_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroMaskedTablePackage_tailTotalTsum_le_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum ≤ 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawRowsZeroMaskedTablePackage_tailTotalTsum_le_zero K

/--
[minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_le_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum ≤ 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_le_zero K

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_le_card K support hsaturated

/--
[rawRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroMaskedTablePackage (d := d) K).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero K

/--
[rawRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum = (rawRowsZeroMaskedTablePackage (d := d) K).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum K

/--
[minimalCubicRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroMaskedTablePackage (d := d) K).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicRowsZeroMaskedTablePackage_tailRemainderSum_eq_zero K

/--
[minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroMaskedTablePackage (d := d) K).tailTotalTsum = (minimalCubicRowsZeroMaskedTablePackage (d := d) K).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicRowsZeroMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum K

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero K support hsaturated

/--
[rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum = (rawZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.rawZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailRemainderSum_eq_zero K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tailTotalTsum = (minimalCubicZeroOneRowsIndicatorMaskedTablePackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorMaskedTablePackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated


-- created on 2026-10-23
