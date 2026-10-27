import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part4
open StatMech StatMech.Exact3D StatMech.Exact3D.BoundedPolymerCase StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample


/--
[zeroOneInterval_upper_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma zeroOneInterval_upper_le_one_eq :
-- imply
  ((zeroOneInterval.upper : ℚ) : ℝ) ≤ 1 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.zeroOneInterval_upper_le_one

/--
[zeroOneInterval_memR_keyImageIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma zeroOneInterval_memR_keyImageIndicator_eq
  [DecidableEq Key]
  {support : Finset α}
  {classifier : α → Key}
  {k : Key} :
-- imply
  zeroOneInterval.MemR (keyImageIndicator support classifier k) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.zeroOneInterval_memR_keyImageIndicator support classifier k

/--
[keyImageIndicatorSplit_additive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma keyImageIndicatorSplit_additive_eq
  [DecidableEq Key]
  {support : Finset α}
  {classifier : α → Key} :
-- imply
  (keyImageIndicatorSplit support classifier).Additive := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.keyImageIndicatorSplit_additive support classifier

/--
[keyImageIndicatorSplit_total_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma keyImageIndicatorSplit_total_nonneg_eq
  [DecidableEq Key]
  {support : Finset α}
  {classifier : α → Key} :
-- imply
  ∀ a, 0 ≤ (keyImageIndicatorSplit support classifier).totalContribution a := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.keyImageIndicatorSplit_total_nonneg support classifier

/--
[keyImageIndicatorSplit_zero_off_saturated_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma keyImageIndicatorSplit_zero_off_saturated_support_eq
  [DecidableEq Key]
  {support : Finset α}
  {classifier : α → Key}
-- given
  (hsaturated : ∀ a, classifier a ∈ support.image classifier → a ∈ support) :
-- imply
  ∀ a, a ∉ support → (keyImageIndicatorSplit support classifier).totalContribution a = 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.keyImageIndicatorSplit_zero_off_saturated_support support classifier hsaturated

/--
[keyImageIndicatorSplit_finite_zero_off_saturated_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma keyImageIndicatorSplit_finite_zero_off_saturated_support_eq
  [DecidableEq Key]
  {support : Finset α}
  {classifier : α → Key}
-- given
  (hsaturated : ∀ a, classifier a ∈ support.image classifier → a ∈ support) :
-- imply
  ∀ a, a ∉ support → (keyImageIndicatorSplit support classifier).finiteContribution a = 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.keyImageIndicatorSplit_finite_zero_off_saturated_support support classifier hsaturated

/--
[keyImageIndicatorSplit_tailEnvelopeOn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma keyImageIndicatorSplit_tailEnvelopeOn_zero_eq
  [DecidableEq Key]
  {support : Finset α}
  {classifier : α → Key} :
-- imply
  (keyImageIndicatorSplit support classifier).TailEnvelopeOn support (fun _ => (0 : ℝ)) := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.keyImageIndicatorSplit_tailEnvelopeOn_zero support classifier

/--
[keyImageIndicatorSplit_tailContribution_nonpos_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma keyImageIndicatorSplit_tailContribution_nonpos_off_support_eq
  [DecidableEq Key]
  {support : Finset α}
  {classifier : α → Key} :
-- imply
  ∀ a, a ∉ support → (keyImageIndicatorSplit support classifier).tailContribution a ≤ 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.keyImageIndicatorSplit_tailContribution_nonpos_off_support support classifier

/--
[zero_tailEnvelope_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma zero_tailEnvelope_sum_le_eq
  {support : Finset α} :
-- imply
  (∑ _a ∈ support, (0 : ℝ)) ≤ 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.zero_tailEnvelope_sum_le support

/--
[generatedStableKeyIndicator_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma generatedStableKeyIndicator_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffStableKey K a ∈ support.image (classifyFiniteCutoffStableKey K) → a ∈ support) :
-- imply
  (∑' a, (keyImageIndicatorSplit support (classifyFiniteCutoffStableKey K)).totalContribution a) ≤ (support.card : ℝ) * 1 + 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.generatedStableKeyIndicator_tsum_total_le K support hsaturated

/--
[generatedMinimalCubicStableKeyIndicator_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma generatedMinimalCubicStableKeyIndicator_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffMinimalCubicStableKey K a ∈ support.image (classifyFiniteCutoffMinimalCubicStableKey K) → a ∈ support) :
-- imply
  (∑' a, (keyImageIndicatorSplit support (classifyFiniteCutoffMinimalCubicStableKey K)).totalContribution a) ≤ (support.card : ℝ) * 1 + 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.generatedMinimalCubicStableKeyIndicator_tsum_total_le K support hsaturated

/--
[generatedBoundedCaseIndicator_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma generatedBoundedCaseIndicator_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCoordinate K a ∈ support.image (classifyFiniteCutoffCoordinate K) → a ∈ support) :
-- imply
  (∑' a, (keyImageIndicatorSplit support (classifyFiniteCutoffCoordinate K)).totalContribution a) ≤ (support.card : ℝ) * 1 + 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.generatedBoundedCaseIndicator_tsum_total_le K support hsaturated

/--
[generatedCubicClassIndicator_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean)
-/
@[path]
private lemma generatedCubicClassIndicator_tsum_total_le_eq
  {d : ℕ}
  {K : TailCutoff}
  {support : Finset (FiniteCutoffCoordinate d K)}
-- given
  (hsaturated : ∀ a, classifyFiniteCutoffCubicClass K a ∈ support.image (classifyFiniteCutoffCubicClass K) → a ∈ support) :
-- imply
  (∑' a, (keyImageIndicatorSplit support (classifyFiniteCutoffCubicClass K)).totalContribution a) ≤ (support.card : ℝ) * 1 + 0 := by
-- proof
  apply StatMech.Exact3D.BoundedPolymerCase.GeneratedTableTailBridgeExample.generatedCubicClassIndicator_tsum_total_le K support hsaturated


-- created on 2026-10-23
