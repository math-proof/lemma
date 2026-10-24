import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.InfiniteTailStableKeyPackageExample
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailStableKeyPackageExample


/--
[mem_rowKeyFinset_map_zeroOneRowOfKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma mem_rowKeyFinset_map_zeroOneRowOfKey_eq
  {maxDegree maxRange : ℕ}
  {s : Finset (StableKey maxDegree maxRange)}
  {k : StableKey maxDegree maxRange} :
-- imply
  k ∈ stableKeyIntervalRowKeyFinset (s.toList.map zeroOneRowOfKey) ↔ k ∈ s := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.mem_rowKeyFinset_map_zeroOneRowOfKey s k

/--
[rawZeroOneRows_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRows_exactKeySet_eq
  {d R maxDegree maxRange : ℕ} :
-- imply
  StableKeyIntervalRow.ExactKeySet (rawZeroOneRows d R maxDegree maxRange) ((exhaustiveTable d R maxDegree maxRange).image stableKey) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRows_exactKeySet d R maxDegree maxRange

/--
[minimalCubicZeroOneRows_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRows_exactKeySet_eq
  {d R maxDegree maxRange : ℕ} :
-- imply
  StableKeyIntervalRow.ExactKeySet (minimalCubicZeroOneRows d R maxDegree maxRange) ((exhaustiveCubicClassTable d R maxDegree maxRange).image minimalCubicStableKey) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRows_exactKeySet d R maxDegree maxRange

/--
[rawZeroOneRows_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRows_cover_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  stableKey c ∈ stableKeyIntervalRowKeyFinset (rawZeroOneRows d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRows_cover d R maxDegree maxRange c

/--
[minimalCubicZeroOneRows_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRows_cover_eq
  {d R maxDegree maxRange : ℕ}
  {c : BoundedPolymerCase d R maxDegree maxRange} :
-- imply
  classifyByMinimalCubicStableKey c ∈ stableKeyIntervalRowKeyFinset (minimalCubicZeroOneRows d R maxDegree maxRange) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRows_cover d R maxDegree maxRange c

/--
[rawZeroOneRows_row_sound_keyImageIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRows_row_sound_keyImageIndicator_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)}
  {row : StableKeyIntervalRow K.maxDegree K.maxRange}
-- given
  (hrow : row ∈ rawZeroOneRows d K.radius K.maxDegree K.maxRange) :
-- imply
  row.interval.MemR (keyImageIndicator support (classifyFiniteCutoffStableKey K) row.key.toKey) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRows_row_sound_keyImageIndicator K support row hrow

/--
[minimalCubicZeroOneRows_row_sound_keyImageIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRows_row_sound_keyImageIndicator_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)}
  {row : StableKeyIntervalRow K.maxDegree K.maxRange}
-- given
  (hrow : row ∈ minimalCubicZeroOneRows d K.radius K.maxDegree K.maxRange) :
-- imply
  row.interval.MemR (keyImageIndicator support (classifyFiniteCutoffMinimalCubicStableKey K) row.key.toKey) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRows_row_sound_keyImageIndicator K support row hrow

/--
[rawZeroOneRows_row_upper_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRows_row_upper_one_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ rawZeroOneRows d R maxDegree maxRange) :
-- imply
  ((row.interval.upper : ℚ) : ℝ) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRows_row_upper_one d R maxDegree maxRange row hrow

/--
[minimalCubicZeroOneRows_row_upper_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRows_row_upper_one_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ minimalCubicZeroOneRows d R maxDegree maxRange) :
-- imply
  ((row.interval.upper : ℚ) : ℝ) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRows_row_upper_one d R maxDegree maxRange row hrow

/--
[rawRowsZeroInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_finiteChecks K

/--
[rawRowsZeroInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_finiteCaseChecks K

/--
[rawRowsZeroInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_tailBounds K

/--
[rawRowsZeroInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_fixedPointEnclosure K

/--
[rawRowsZeroInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_linearizationEnclosure K

/--
[rawRowsZeroInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_hyperbolicSplitting K

/--
[rawRowsZeroInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_orbitEntry K

/--
[minimalCubicRowsZeroInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_finiteChecks K

/--
[minimalCubicRowsZeroInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_finiteCaseChecks K

/--
[minimalCubicRowsZeroInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_tailBounds K

/--
[minimalCubicRowsZeroInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_fixedPointEnclosure K

/--
[minimalCubicRowsZeroInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_linearizationEnclosure K

/--
[minimalCubicRowsZeroInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_hyperbolicSplitting K

/--
[minimalCubicRowsZeroInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_orbitEntry K

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteChecks K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_tailBounds K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_finiteCaseChecks K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailBounds K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_fixedPointEnclosure K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_linearizationEnclosure K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hyperbolicSplitting K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_orbitEntry K support hsaturated

/--
[rawRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).tableCertifiedTotalBound = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero K

/--
[minimalCubicRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tableCertifiedTotalBound = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_tableCertifiedTotalBound_eq_zero K

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tableCertifiedTotalBound_eq_card K support hsaturated

/--
[rawRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum ≤ 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero K

/--
[minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum ≤ 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_le_zero K

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_le_card K support hsaturated

/--
[rawRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero K

/--
[rawRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum = (rawRowsZeroInfiniteTailPackage (d := d) K).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum K

/--
[minimalCubicRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_tailRemainderSum_eq_zero K

/--
[minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailTotalTsum = (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum K

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum = (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailRemainderSum_eq_zero K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum = (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  ((rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [rawZeroOneRowsIndicatorInfiniteTailPackage, ofExternalStableKeyRowsFiniteCutoffStableKey])).finiteBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  ((rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [rawZeroOneRowsIndicatorInfiniteTailPackage, ofExternalStableKeyRowsFiniteCutoffStableKey] )).tableCertifiedTotalBound = (support.card : ℝ) * 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  ((minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage, ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).finiteBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_eq_two K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  ((minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [minimalCubicZeroOneRowsIndicatorInfiniteTailPackage, ofExternalStableKeyRowsFiniteCutoffMinimalCubic] )).tableCertifiedTotalBound = (support.card : ℝ) * 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_relaxedFiniteBound_budget_eq K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two K support hsaturated

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two K support hsaturated

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two K support hsaturated

/--
[rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  ((rawRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound (tailBound' := 1) (by norm_num [rawRowsZeroInfiniteTailPackage, ofExternalStableKeyRowsFiniteCutoffStableKey])).tailBound = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one K

/--
[rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  ((rawRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound (tailBound' := 1) (by norm_num [rawRowsZeroInfiniteTailPackage, ofExternalStableKeyRowsFiniteCutoffStableKey])).tailTotalTsum ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one K

/--
[minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  ((minimalCubicRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound (tailBound' := 1) (by norm_num [minimalCubicRowsZeroInfiniteTailPackage, ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).tailBound = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailBound_eq_one K

/--
[minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  ((minimalCubicRowsZeroInfiniteTailPackage (d := d) K).with_larger_tailBound (tailBound' := 1) (by norm_num [minimalCubicRowsZeroInfiniteTailPackage, ofExternalStableKeyRowsFiniteCutoffMinimalCubic])).tailTotalTsum ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_relaxedTailBound_tailTotalTsum_le_one K

/--
[rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope (d := d) K).tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two K

/--
[rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope (d := d) K).certificate = (rawRowsZeroInfiniteTailPackage (d := d) K).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq K

/--
[rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsZeroInfiniteTailPackage_replacedTailEnvelope (d := d) K).tailTotalTsum ≤ 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two K

/--
[minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope (d := d) K).tableCertifiedTotalBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_budget_eq_two K

/--
[minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope (d := d) K).certificate = (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_certificate_eq K

/--
[minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope (d := d) K).tailTotalTsum ≤ 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_replacedTailEnvelope_tsum_le_two K

/--
[rawRowsZeroInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.RGToExponentBridge correlationLength) :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_valid_of_bridge K correlationLength hbridge

/--
[rawRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge K correlationLength hbridge

/--
[minimalCubicRowsZeroInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.RGToExponentBridge correlationLength) :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_valid_of_bridge K correlationLength hbridge

/--
[minimalCubicRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_hasCriticalNu_of_bridge K correlationLength hbridge

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[rawRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.predictedExponent) :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu K correlationLength hν

/--
[rawRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.predictedExponent) :
-- imply
  (rawRowsZeroInfiniteTailPackage (d := d) K).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu K correlationLength hν

/--
[minimalCubicRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.predictedExponent) :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu K correlationLength hν

/--
[minimalCubicRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.predictedExponent) :
-- imply
  (minimalCubicRowsZeroInfiniteTailPackage (d := d) K).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicRowsZeroInfiniteTailPackage_valid_of_hasCriticalNu K correlationLength hν

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (rawZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.rawZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (minimalCubicZeroOneRowsIndicatorInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailStableKeyPackageExample.minimalCubicZeroOneRowsIndicatorInfiniteTailPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν


-- created on 2026-10-23
