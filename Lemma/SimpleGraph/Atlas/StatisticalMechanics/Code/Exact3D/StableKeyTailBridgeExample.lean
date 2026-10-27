import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample.Part3
open StatMech StatMech.Exact3D StatMech.Exact3D.BoundedPolymerCase StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample


/--
[zeroSplit_additive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma zeroSplit_additive_eq
  {d : ℕ}
  {K : TailCutoff} :
-- imply
  (zeroSplit (d := d) K).Additive := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.zeroSplit_additive K

/--
[zeroSplit_total_zero_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma zeroSplit_total_zero_off_support_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  ∀ a, a ∉ support → (zeroSplit (d := d) K).totalContribution a = 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.zeroSplit_total_zero_off_support K support

/--
[zeroSplit_tailEnvelopeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma zeroSplit_tailEnvelopeOn_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (zeroSplit (d := d) K).TailEnvelopeOn support (fun _ => (0 : ℝ)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.zeroSplit_tailEnvelopeOn K support

/--
[zeroSplit_tailContribution_nonpos_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma zeroSplit_tailContribution_nonpos_off_support_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  ∀ a, a ∉ support → (zeroSplit (d := d) K).tailContribution a ≤ 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.zeroSplit_tailContribution_nonpos_off_support K support

/--
[zeroSplit_total_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma zeroSplit_total_nonneg_eq
  {d : ℕ}
  {K : TailCutoff} :
-- imply
  ∀ a, 0 ≤ (zeroSplit (d := d) K).totalContribution a := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.zeroSplit_total_nonneg K

/--
[zero_tailEnvelope_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma zero_tailEnvelope_sum_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (∑ _a ∈ support, (0 : ℝ)) ≤ 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.zero_tailEnvelope_sum_le K support

/--
[indicatorTailSplit_finiteContribution_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma indicatorTailSplit_finiteContribution_eq_zero_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  ∀ c, (indicatorTailSplit (d := d) K support).finiteContribution c = 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.indicatorTailSplit_finiteContribution_eq_zero K support

/--
[singletonEmptySupport_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma singletonEmptySupport_card_eq
  {d : ℕ}
  {K : TailCutoff} :
-- imply
  (singletonEmptySupport (d := d) K).card = 1 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.singletonEmptySupport_card K

/--
[indicatorTailSplit_total_emptyFiniteCutoffCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma indicatorTailSplit_total_emptyFiniteCutoffCoordinate_eq
  {d : ℕ}
  {K : TailCutoff} :
-- imply
  (indicatorTailSplit (d := d) K (singletonEmptySupport (d := d) K)).totalContribution (emptyFiniteCutoffCoordinate d K) = (1 : ℝ) / 10 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.indicatorTailSplit_total_emptyFiniteCutoffCoordinate K

/--
[indicatorTailSplit_additive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma indicatorTailSplit_additive_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (indicatorTailSplit (d := d) K support).Additive := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.indicatorTailSplit_additive K support

/--
[indicatorTailSplit_total_zero_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma indicatorTailSplit_total_zero_off_support_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  ∀ a, a ∉ support → (indicatorTailSplit (d := d) K support).totalContribution a = 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.indicatorTailSplit_total_zero_off_support K support

/--
[indicatorTailSplit_tailEnvelopeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma indicatorTailSplit_tailEnvelopeOn_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (indicatorTailSplit (d := d) K support).TailEnvelopeOn support (fun _ => (1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.indicatorTailSplit_tailEnvelopeOn K support

/--
[indicatorTailSplit_total_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma indicatorTailSplit_total_nonneg_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  ∀ a, 0 ≤ (indicatorTailSplit (d := d) K support).totalContribution a := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.indicatorTailSplit_total_nonneg K support

/--
[indicatorTailSplit_tailEnvelope_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma indicatorTailSplit_tailEnvelope_sum_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (∑ _a ∈ support, ((1 : ℝ) / 10)) ≤ (support.card : ℝ) * ((1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.indicatorTailSplit_tailEnvelope_sum_le K support

/--
[rawRows_row_upper_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma rawRows_row_upper_zero_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ StableKeyCertificateExample.rawRows d R maxDegree maxRange) :
-- imply
  ((row.interval.upper : ℚ) : ℝ) ≤ 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.rawRows_row_upper_zero d R maxDegree maxRange row hrow

/--
[rawRows_row_upper_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma rawRows_row_upper_one_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ StableKeyCertificateExample.rawRows d R maxDegree maxRange) :
-- imply
  ((row.interval.upper : ℚ) : ℝ) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.rawRows_row_upper_one d R maxDegree maxRange row hrow

/--
[minimalCubicRows_row_upper_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma minimalCubicRows_row_upper_zero_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ StableKeyCertificateExample.minimalCubicRows d R maxDegree maxRange) :
-- imply
  ((row.interval.upper : ℚ) : ℝ) ≤ 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.minimalCubicRows_row_upper_zero d R maxDegree maxRange row hrow

/--
[minimalCubicRows_row_upper_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma minimalCubicRows_row_upper_one_eq
  {d R maxDegree maxRange : ℕ}
  {row : StableKeyIntervalRow maxDegree maxRange}
-- given
  (hrow : row ∈ StableKeyCertificateExample.minimalCubicRows d R maxDegree maxRange) :
-- imply
  ((row.interval.upper : ℚ) : ℝ) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.minimalCubicRows_row_upper_one d R maxDegree maxRange row hrow

/--
[rawRows_zero_finiteTableUpperBound_exactKeySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma rawRows_zero_finiteTableUpperBound_exactKeySet_eq
  {d : ℕ}
  {K : TailCutoff} :
-- imply
  FiniteTableUpperBound (externalStableKeyIntervalRowTable (StableKeyCertificateExample.rawRows d K.radius K.maxDegree K.maxRange) StableKeyCertificateExample.zeroInterval) (classifyFiniteCutoffStableKey (d := d) K) (fun _ : FiniteCutoffCoordinate d K => (0 : ℝ)) 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.rawRows_zero_finiteTableUpperBound_exactKeySet K

/--
[rawRows_zero_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma rawRows_zero_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (∑' a, (zeroSplit (d := d) K).totalContribution a) ≤ (support.card : ℝ) * 0 + 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.rawRows_zero_tsum_total_le K support

/--
[minimalCubicRows_zero_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma minimalCubicRows_zero_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (∑' a, (zeroSplit (d := d) K).totalContribution a) ≤ (support.card : ℝ) * 0 + 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.minimalCubicRows_zero_tsum_total_le K support

/--
[rawRows_indicatorTail_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma rawRows_indicatorTail_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (∑' a, (indicatorTailSplit (d := d) K support).totalContribution a) ≤ (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.rawRows_indicatorTail_tsum_total_le K support

/--
[minimalCubicRows_indicatorTail_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma minimalCubicRows_indicatorTail_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)} :
-- imply
  (∑' a, (indicatorTailSplit (d := d) K support).totalContribution a) ≤ (support.card : ℝ) * 1 + (support.card : ℝ) * ((1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.minimalCubicRows_indicatorTail_tsum_total_le K support

/--
[rawRows_singletonIndicatorTail_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma rawRows_singletonIndicatorTail_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff} :
-- imply
  (∑' a, (indicatorTailSplit (d := d) K (singletonEmptySupport (d := d) K)).totalContribution a) ≤ (1 : ℝ) + (1 : ℝ) / 10 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.rawRows_singletonIndicatorTail_tsum_total_le K

/--
[minimalCubicRows_singletonIndicatorTail_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean)
-/
@[path]
private lemma minimalCubicRows_singletonIndicatorTail_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff} :
-- imply
  (∑' a, (indicatorTailSplit (d := d) K (singletonEmptySupport (d := d) K)).totalContribution a) ≤ (1 : ℝ) + (1 : ℝ) / 10 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.StableKeyTailBridgeExample.minimalCubicRows_singletonIndicatorTail_tsum_total_le K


-- created on 2026-10-23
