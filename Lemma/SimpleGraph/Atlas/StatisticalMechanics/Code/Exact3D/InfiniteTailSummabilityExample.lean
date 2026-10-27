import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part5
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailSummabilityExample


/--
[geometricHalfTailWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma geometricHalfTailWeight_nonneg_eq
  {n : ℕ} :
-- imply
  0 ≤ geometricHalfTailWeight n := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg n

/--
[geometricHalfTailWeight_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma geometricHalfTailWeight_summable_eq :
-- imply
  Summable geometricHalfTailWeight := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.geometricHalfTailWeight_summable

/--
[geometricHalfTailWeight_tsum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma geometricHalfTailWeight_tsum_eq_one_eq :
-- imply
  (∑' n : ℕ, geometricHalfTailWeight n) = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.geometricHalfTailWeight_tsum_eq_one

/--
[geometricHalfInfiniteTailCertificate_tsum_weight_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma geometricHalfInfiniteTailCertificate_tsum_weight_le_one_eq :
-- imply
  (∑' n : ℕ, geometricHalfInfiniteTailCertificate.weight n) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate_tsum_weight_le_one

/--
[geometricHalfInfiniteTailCertificateFromEnvelope_tsum_weight_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma geometricHalfInfiniteTailCertificateFromEnvelope_tsum_weight_le_one_eq :
-- imply
  (∑' n : ℕ, geometricHalfInfiniteTailCertificateFromEnvelope.weight n) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificateFromEnvelope_tsum_weight_le_one

/--
[maskedGeometricHalfTailWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma maskedGeometricHalfTailWeight_nonneg_eq
  {n : ℕ} :
-- imply
  0 ≤ maskedGeometricHalfTailWeight n := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_nonneg n

/--
[maskedGeometricHalfTailWeight_le_geometricHalfTailWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma maskedGeometricHalfTailWeight_le_geometricHalfTailWeight_eq
  {n : ℕ} :
-- imply
  maskedGeometricHalfTailWeight n ≤ geometricHalfTailWeight n := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_le_geometricHalfTailWeight n

/--
[maskedGeometricHalfTailWeight_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma maskedGeometricHalfTailWeight_summable_eq :
-- imply
  Summable maskedGeometricHalfTailWeight := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_summable

/--
[maskedGeometricHalfTailWeight_tsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma maskedGeometricHalfTailWeight_tsum_le_one_eq :
-- imply
  (∑' n : ℕ, maskedGeometricHalfTailWeight n) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_tsum_le_one

/--
[geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tailBound_eq :
-- imply
  geometricHalfInfiniteTailCertificateFromMaskedEnvelope.tailBound = 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tailBound

/--
[geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tsum_weight_le_prefixSum_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tsum_weight_le_prefixSum_add_one_eq :
-- imply
  (∑' n : ℕ, geometricHalfInfiniteTailCertificateFromMaskedEnvelope.weight n) ≤ geometricHalfInfiniteTailCertificateFromMaskedEnvelope.prefixSum + 1 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tsum_weight_le_prefixSum_add_one

/--
[singletonFiniteAsInfinite_prefixSum_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma singletonFiniteAsInfinite_prefixSum_eq_three_eq :
-- imply
  singletonFiniteAsInfinite.prefixSum = 3 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.singletonFiniteAsInfinite_prefixSum_eq_three

/--
[singletonFiniteAsInfinite_tsum_weight_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean)
-/
@[path]
private lemma singletonFiniteAsInfinite_tsum_weight_le_three_eq :
-- imply
  (∑' n : ℕ, singletonFiniteAsInfinite.weight n) ≤ 3 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailSummabilityExample.singletonFiniteAsInfinite_tsum_weight_le_three


-- created on 2026-10-23
