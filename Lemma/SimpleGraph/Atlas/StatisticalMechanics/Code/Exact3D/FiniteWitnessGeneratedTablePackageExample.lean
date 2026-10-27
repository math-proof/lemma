import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessGeneratedTablePackageExample
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample


/--
[generatedBoundedCaseIndicatorPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  RGCertificate.FiniteChecks ((generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_finiteChecks K support hsaturated

/--
[generatedCubicClassIndicatorPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  RGCertificate.FiniteChecks ((generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_finiteChecks K support hsaturated

/--
[generatedStableKeyIndicatorPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  RGCertificate.FiniteChecks ((generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_finiteChecks K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  RGCertificate.FiniteChecks ((generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_finiteChecks K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_finiteCaseChecks K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_tailBounds K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_fixedPointEnclosure K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_linearizationEnclosure K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_hyperbolicSplitting K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_orbitEntry K support hsaturated

/--
[generatedCubicClassIndicatorPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_finiteCaseChecks K support hsaturated

/--
[generatedCubicClassIndicatorPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_tailBounds K support hsaturated

/--
[generatedCubicClassIndicatorPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_fixedPointEnclosure K support hsaturated

/--
[generatedCubicClassIndicatorPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_linearizationEnclosure K support hsaturated

/--
[generatedCubicClassIndicatorPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_hyperbolicSplitting K support hsaturated

/--
[generatedCubicClassIndicatorPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_orbitEntry K support hsaturated

/--
[generatedStableKeyIndicatorPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_finiteCaseChecks K support hsaturated

/--
[generatedStableKeyIndicatorPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_tailBounds K support hsaturated

/--
[generatedStableKeyIndicatorPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_fixedPointEnclosure K support hsaturated

/--
[generatedStableKeyIndicatorPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_linearizationEnclosure K support hsaturated

/--
[generatedStableKeyIndicatorPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_hyperbolicSplitting K support hsaturated

/--
[generatedStableKeyIndicatorPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_orbitEntry K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_finiteCaseChecks K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_tailBounds K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_fixedPointEnclosure K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_linearizationEnclosure K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_hyperbolicSplitting K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_orbitEntry K support hsaturated

/--
[generatedStableKeyIndicatorPackage_predictedExponent_eq_boundedCase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_predictedExponent_eq_boundedCase_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hstable : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbounded : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hstable).certificate.predictedExponent = (generatedBoundedCaseIndicatorPackage (d := d) K support hbounded).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_predictedExponent_eq_boundedCase K support hstable hbounded

/--
[generatedBoundedCaseIndicatorPackage_tailPrefixSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_tailPrefixSum_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).tailPrefixSum = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_tailPrefixSum_eq K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_tailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_tailBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).tailBudget = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_tailBudget_eq K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_tailCertifiedTotalBound_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).tailCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_tailCertifiedTotalBound_eq K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_tail_tsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_tail_tsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (∑' a, (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).tailCertificate.weight a) ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_tail_tsum_le_card K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedCubicClassIndicatorPackage_tailPrefixSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_tailPrefixSum_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).tailPrefixSum = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_tailPrefixSum_eq K support hsaturated

/--
[generatedCubicClassIndicatorPackage_tailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_tailBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).tailBudget = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_tailBudget_eq K support hsaturated

/--
[generatedCubicClassIndicatorPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_tailCertifiedTotalBound_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).tailCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_tailCertifiedTotalBound_eq K support hsaturated

/--
[generatedCubicClassIndicatorPackage_tail_tsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_tail_tsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (∑' a, (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).tailCertificate.weight a) ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_tail_tsum_le_card K support hsaturated

/--
[generatedCubicClassIndicatorPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedStableKeyIndicatorPackage_tailPrefixSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_tailPrefixSum_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).tailPrefixSum = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_tailPrefixSum_eq K support hsaturated

/--
[generatedStableKeyIndicatorPackage_tailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_tailBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).tailBudget = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_tailBudget_eq K support hsaturated

/--
[generatedStableKeyIndicatorPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_tailCertifiedTotalBound_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).tailCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_tailCertifiedTotalBound_eq K support hsaturated

/--
[generatedStableKeyIndicatorPackage_tail_tsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_tail_tsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (∑' a, (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).tailCertificate.weight a) ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_tail_tsum_le_card K support hsaturated

/--
[generatedStableKeyIndicatorPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_tailPrefixSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_tailPrefixSum_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).tailPrefixSum = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_tailPrefixSum_eq K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_tailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_tailBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).tailBudget = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_tailBudget_eq K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_tailCertifiedTotalBound_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).tailCertifiedTotalBound = (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_tailCertifiedTotalBound_eq K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_tail_tsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_tail_tsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (∑' a, (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).tailCertificate.weight a) ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_tail_tsum_le_card K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicatorPackage_tailTotalTsum_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_tailTotalTsum_le_card_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).tailTotalTsum ≤ (support.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_tailTotalTsum_le_card K support hsaturated

/--
[generatedBoundedCaseIndicatorPackage_rgToExponentBridge_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_rgToExponentBridge_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  RGCertificate.RGToExponentBridge ((generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_rgToExponentBridge_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedStableKeyIndicatorPackage_rgToExponentBridge_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_rgToExponentBridge_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  RGCertificate.RGToExponentBridge ((generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_rgToExponentBridge_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedCubicClassIndicatorPackage_rgToExponentBridge_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_rgToExponentBridge_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  RGCertificate.RGToExponentBridge ((generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_rgToExponentBridge_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedMinimalCubicStableKeyIndicatorPackage_rgToExponentBridge_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_rgToExponentBridge_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  RGCertificate.RGToExponentBridge ((generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_rgToExponentBridge_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedBoundedCaseIndicatorPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  RGCertificate.Valid ((generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedStableKeyIndicatorPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  RGCertificate.Valid ((generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedCubicClassIndicatorPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  RGCertificate.Valid ((generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedMinimalCubicStableKeyIndicatorPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  RGCertificate.Valid ((generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_valid_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedBoundedCaseIndicatorPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedCubicClassIndicatorPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedStableKeyIndicatorPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedMinimalCubicStableKeyIndicatorPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hbridge : RGCertificate.RGToExponentBridge ((generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate) correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_hasCriticalNu_of_bridge K support hsaturated correlationLength hbridge

/--
[generatedBoundedCaseIndicatorPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedBoundedCaseIndicatorPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicatorPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedBoundedCaseIndicatorPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedBoundedCaseIndicatorPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedCubicClassIndicatorPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedCubicClassIndicatorPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicatorPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedCubicClassIndicatorPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedCubicClassIndicatorPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedStableKeyIndicatorPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedStableKeyIndicatorPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicatorPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedStableKeyIndicatorPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedMinimalCubicStableKeyIndicatorPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_rgToExponentBridge_of_hasCriticalNu K support hsaturated correlationLength hν

/--
[generatedMinimalCubicStableKeyIndicatorPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessGeneratedTablePackageExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicatorPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support)
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.predictedExponent) :
-- imply
  (generatedMinimalCubicStableKeyIndicatorPackage (d := d) K support hsaturated).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessGeneratedTablePackageExample.generatedMinimalCubicStableKeyIndicatorPackage_valid_of_hasCriticalNu K support hsaturated correlationLength hν


-- created on 2026-10-23
