import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessStableKeyPackageExample
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessStableKeyPackageExample


/--
[rawRowsIndicatorTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_finiteChecks K support

/--
[minimalCubicRowsIndicatorTailPackage_finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_finiteChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  RGCertificate.FiniteChecks ((minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_finiteChecks K support

/--
[rawRowsIndicatorTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_finiteCaseChecks K support

/--
[rawRowsIndicatorTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_tailBounds K support

/--
[rawRowsIndicatorTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_fixedPointEnclosure K support

/--
[rawRowsIndicatorTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_linearizationEnclosure K support

/--
[rawRowsIndicatorTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_hyperbolicSplitting K support

/--
[rawRowsIndicatorTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_orbitEntry K support

/--
[minimalCubicRowsIndicatorTailPackage_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_finiteCaseChecks_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_finiteCaseChecks K support

/--
[minimalCubicRowsIndicatorTailPackage_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_tailBounds_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_tailBounds K support

/--
[minimalCubicRowsIndicatorTailPackage_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_fixedPointEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_fixedPointEnclosure K support

/--
[minimalCubicRowsIndicatorTailPackage_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_linearizationEnclosure_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_linearizationEnclosure K support

/--
[minimalCubicRowsIndicatorTailPackage_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_hyperbolicSplitting_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_hyperbolicSplitting K support

/--
[minimalCubicRowsIndicatorTailPackage_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_orbitEntry_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_orbitEntry K support

/--
[rawRowsIndicatorTailPackage_tailPrefixSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_tailPrefixSum_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).tailPrefixSum = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_tailPrefixSum_eq K support

/--
[rawRowsIndicatorTailPackage_tailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_tailBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).tailBudget = (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_tailBudget_eq K support

/--
[rawRowsIndicatorTailPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_tailCertifiedTotalBound_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).tailCertifiedTotalBound = (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_tailCertifiedTotalBound_eq K support

/--
[minimalCubicRowsIndicatorTailPackage_tailPrefixSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_tailPrefixSum_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).tailPrefixSum = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_tailPrefixSum_eq K support

/--
[minimalCubicRowsIndicatorTailPackage_tailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_tailBudget_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).tailBudget = (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_tailBudget_eq K support

/--
[minimalCubicRowsIndicatorTailPackage_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_tailCertifiedTotalBound_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).tailCertifiedTotalBound = (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_tailCertifiedTotalBound_eq K support

/--
[rawRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K (singletonEmptySupport (d := d) K)).tailCertifiedTotalBound = (11 : ℝ) / 10 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq K

/--
[rawRowsIndicatorTailPackage_singleton_tail_tsum_le_11_div_10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_singleton_tail_tsum_le_11_div_10_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (∑' a, (rawRowsIndicatorTailPackage (d := d) K (singletonEmptySupport (d := d) K)).tailCertificate.weight a) ≤ (11 : ℝ) / 10 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_singleton_tail_tsum_le_11_div_10 K

/--
[minimalCubicRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K (singletonEmptySupport (d := d) K)).tailCertifiedTotalBound = (11 : ℝ) / 10 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_singleton_tailCertifiedTotalBound_eq K

/--
[minimalCubicRowsIndicatorTailPackage_singleton_tail_tsum_le_11_div_10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_singleton_tail_tsum_le_11_div_10_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)] :
-- imply
  (∑' a, (minimalCubicRowsIndicatorTailPackage (d := d) K (singletonEmptySupport (d := d) K)).tailCertificate.weight a) ≤ (11 : ℝ) / 10 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_singleton_tail_tsum_le_11_div_10 K

/--
[rawRowsIndicatorTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : RGCertificate.RGToExponentBridge ((rawRowsIndicatorTailPackage (d := d) K support).certificate) correlationLength) :
-- imply
  RGCertificate.Valid ((rawRowsIndicatorTailPackage (d := d) K support).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_valid_of_bridge K support correlationLength hbridge

/--
[rawRowsIndicatorTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : RGCertificate.RGToExponentBridge ((rawRowsIndicatorTailPackage (d := d) K support).certificate) correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawRowsIndicatorTailPackage (d := d) K support).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_hasCriticalNu_of_bridge K support correlationLength hbridge

/--
[minimalCubicRowsIndicatorTailPackage_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_valid_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : RGCertificate.RGToExponentBridge ((minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate) correlationLength) :
-- imply
  RGCertificate.Valid ((minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate) correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_valid_of_bridge K support correlationLength hbridge

/--
[minimalCubicRowsIndicatorTailPackage_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_hasCriticalNu_of_bridge_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : RGCertificate.RGToExponentBridge ((minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate) correlationLength) :
-- imply
  HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_hasCriticalNu_of_bridge K support correlationLength hbridge

/--
[rawRowsIndicatorTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawRowsIndicatorTailPackage (d := d) K support).certificate.predictedExponent) :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_rgToExponentBridge_of_hasCriticalNu K support correlationLength hν

/--
[rawRowsIndicatorTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma rawRowsIndicatorTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (rawRowsIndicatorTailPackage (d := d) K support).certificate.predictedExponent) :
-- imply
  (rawRowsIndicatorTailPackage (d := d) K support).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.rawRowsIndicatorTailPackage_valid_of_hasCriticalNu K support correlationLength hν

/--
[minimalCubicRowsIndicatorTailPackage_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_rgToExponentBridge_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.predictedExponent) :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_rgToExponentBridge_of_hasCriticalNu K support correlationLength hν

/--
[minimalCubicRowsIndicatorTailPackage_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessStableKeyPackageExample.lean)
-/
@[path]
private lemma minimalCubicRowsIndicatorTailPackage_valid_of_hasCriticalNu_eq
  {d : ℕ}
  {K : TailCutoff}
  [DecidableEq (FiniteCutoffCoordinate d K)]
  {support : Finset (FiniteCutoffCoordinate d K)}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) correlationLength (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.predictedExponent) :
-- imply
  (minimalCubicRowsIndicatorTailPackage (d := d) K support).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessStableKeyPackageExample.minimalCubicRowsIndicatorTailPackage_valid_of_hasCriticalNu K support correlationLength hν


-- created on 2026-10-23
