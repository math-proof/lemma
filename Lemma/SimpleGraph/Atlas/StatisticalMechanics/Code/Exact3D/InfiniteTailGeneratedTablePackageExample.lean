import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.InfiniteTailGeneratedTablePackageExample
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample


/--
[generatedBoundedCaseInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_finiteChecks K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_finiteChecks K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_finiteChecks K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_finiteChecks K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_finiteCaseChecks K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_tailBounds K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_fixedPointEnclosure K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_linearizationEnclosure K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_hyperbolicSplitting K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_orbitEntry K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_finiteCaseChecks K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_tailBounds K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_fixedPointEnclosure K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_linearizationEnclosure K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_hyperbolicSplitting K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_orbitEntry K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_finiteCaseChecks K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_tailBounds K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_fixedPointEnclosure K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_linearizationEnclosure K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_hyperbolicSplitting K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_orbitEntry K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_finiteCaseChecks K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_tailBounds K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_fixedPointEnclosure K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_linearizationEnclosure K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_hyperbolicSplitting K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_orbitEntry K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_predictedExponent_eq_boundedCase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_predictedExponent_eq_boundedCase_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hstable : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbounded : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hstable).certificate.predictedExponent = (generatedBoundedCaseInfiniteTailPackage (d := d) K support hbounded).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_predictedExponent_eq_boundedCase K support hstable hbounded

/--
[generatedBoundedCaseInfiniteTailPackage_tableCertifiedTotalBound_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_tableCertifiedTotalBound_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_tableCertifiedTotalBound_eq_card K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_tableCertifiedTotalBound_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_tableCertifiedTotalBound_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_tableCertifiedTotalBound_eq_card K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_tableCertifiedTotalBound_eq_card K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_tailRemainderSum_eq_zero K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum = (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_tailRemainderSum_eq_zero K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum = (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum = (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_tailRemainderSum_eq_zero K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).tailTotalTsum = (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_tailTotalTsum_eq_tailPrefixSum K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  ((generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [generatedBoundedCaseInfiniteTailPackage, ofGeneratedIntervalTableFiniteCutoff])).finiteBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_eq_two K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  ((generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [generatedBoundedCaseInfiniteTailPackage, ofGeneratedIntervalTableFiniteCutoff])).tableCertifiedTotalBound = (support.card : ℝ) * 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_relaxedFiniteBound_budget_eq K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  ((generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [generatedCubicClassInfiniteTailPackage, ofGeneratedCubicIntervalTableFiniteCutoff])).finiteBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_eq_two K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  ((generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [generatedCubicClassInfiniteTailPackage, ofGeneratedCubicIntervalTableFiniteCutoff])).tableCertifiedTotalBound = (support.card : ℝ) * 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_relaxedFiniteBound_budget_eq K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  ((generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [generatedStableKeyInfiniteTailPackage, ofGeneratedStableKeyIntervalTableFiniteCutoff])).finiteBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  ((generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [generatedStableKeyInfiniteTailPackage, ofGeneratedStableKeyIntervalTableFiniteCutoff])).tableCertifiedTotalBound = (support.card : ℝ) * 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  ((generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [generatedMinimalCubicStableKeyInfiniteTailPackage, ofGeneratedMinimalCubicStableKeyTableFiniteCutoff])).finiteBound = 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_eq_two K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  ((generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).with_larger_finiteBound (finiteBound' := 2) (by norm_num [generatedMinimalCubicStableKeyInfiniteTailPackage, ofGeneratedMinimalCubicStableKeyTableFiniteCutoff] )).tableCertifiedTotalBound = (support.card : ℝ) * 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_relaxedFiniteBound_budget_eq K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hbridge : (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge K support hsaturated hbridge

/--
[generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_valid_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hvalid : (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_valid K support hsaturated hvalid

/--
[generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu K support hsaturated hν

/--
[generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hbridge : (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge K support hsaturated hbridge

/--
[generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_valid_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hvalid : (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength) :
-- imply
  (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_valid K support hsaturated hvalid

/--
[generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedCubicClassInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu K support hsaturated hν

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge K support hsaturated hbridge

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_valid_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hvalid : (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_valid K support hsaturated hvalid

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu K support hsaturated hν

/--
[generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tableCertifiedTotalBound = (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_budget_eq_card_add_two K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) + 2 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_tsum_le_card_add_two K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate = (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_certificate_eq K support hsaturated

/--
[generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_rgToExponentBridge K support hsaturated hbridge

/--
[generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_valid_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hvalid : (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength) :
-- imply
  (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_valid K support hsaturated hvalid

/--
[generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedStableKeyInfiniteTailPackage_replacedTailEnvelope (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_replacedTailEnvelope_hasCriticalNu K support hsaturated hν

/--
[generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hbridge : (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hbridge : (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedBoundedCaseInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hbridge : (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedBoundedCaseInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hbridge : (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedCubicClassInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hbridge : (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedCubicClassInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hbridge : (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedStableKeyInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedBoundedCaseInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedBoundedCaseInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedBoundedCaseInfiniteTailPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedCubicClassInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedCubicClassInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedCubicClassInfiniteTailPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedStableKeyInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedStableKeyInfiniteTailPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedMinimalCubicStableKeyInfiniteTailPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailGeneratedTablePackageExample.generatedMinimalCubicStableKeyInfiniteTailPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν


-- created on 2026-10-23
