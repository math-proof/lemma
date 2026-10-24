import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[fourColorMaskProfile_middleSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma fourColorMaskProfile_middleSwap_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  fourColorMaskProfile m (middleSwap m c) = fourColorMaskProfile m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.fourColorMaskProfile_middleSwap m c

/--
[rowClass_middleSwap_zero_eq_symmDiff_middleMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma rowClass_middleSwap_zero_eq_symmDiff_middleMask_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  rowClass m (middleSwap m c) 0 = rowClass m c 0 ∆ middleMask m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_middleSwap_zero_eq_symmDiff_middleMask m c

/--
[rightSourcePattern_middleSwap_iff_leftSourcePattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma rightSourcePattern_middleSwap_iff_leftSourcePattern_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {A B : Finset W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  RightSourcePattern ends m A B (middleSwap m c) ↔ LeftSourcePattern ends m A B c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightSourcePattern_middleSwap_iff_leftSourcePattern ends m A B c

/--
[leftSourcePattern_middleSwap_iff_rightSourcePattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma leftSourcePattern_middleSwap_iff_rightSourcePattern_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {A B : Finset W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  LeftSourcePattern ends m A B (middleSwap m c) ↔ RightSourcePattern ends m A B c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftSourcePattern_middleSwap_iff_rightSourcePattern ends m A B c

/--
[card_leftSourceMaskFiber_eq_rightSourceMaskFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftSourceMaskFiber_eq_rightSourceMaskFiber_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Fintype.card (leftSourceMaskFiber ends m j k l zero p) = Fintype.card (rightSourceMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftSourceMaskFiber_eq_rightSourceMaskFiber ends m j k l zero p

/--
[rowsDisconnect_iff_bipartitionDisconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma rowsDisconnect_iff_bipartitionDisconnects_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {u v : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  RowsDisconnect ends m c u v ↔ BipartitionDisconnects ends m (rowClass m c 0) u v := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowsDisconnect_iff_bipartitionDisconnects ends m c u v

/--
[reversalGateBalance_eq_bipartitionIndicators](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma reversalGateBalance_eq_bipartitionIndicators_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  reversalGateBalance ends m j k l zero p c = bipartitionDisconnectIndicator ends m (rowClass m c.1 0 ∆ p.1) k zero - bipartitionDisconnectIndicator ends m (rowClass m c.1 0) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.reversalGateBalance_eq_bipartitionIndicators ends m j k l zero p c

/--
[exists_sourceMaskCycleAction_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma exists_sourceMaskCycleAction_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  ∃ z : sourceMaskCycleSpace ends p, sourceMaskCycleAction ends m j k l zero p c z = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_sourceMaskCycleAction_eq ends m j k l zero p c d

/--
[sourceMaskCycleAction_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sourceMaskCycleAction_difference_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  sourceMaskCycleAction ends m j k l zero p c (sourceMaskCycleDifference ends m j k l zero p c d) = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sourceMaskCycleAction_difference ends m j k l zero p c d

/--
[sourceMaskCycleAction_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sourceMaskCycleAction_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Function.Injective (sourceMaskCycleAction ends m j k l zero p c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sourceMaskCycleAction_injective ends m j k l zero p c

/--
[rowClass_sourceMaskCycleAction_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma rowClass_sourceMaskCycleAction_zero_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
  {z : sourceMaskCycleSpace ends p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  rowClass m (sourceMaskCycleAction ends m j k l zero p c z).1 0 = rowClass m c.1 0 ∆ (z.1.1 ∪ z.2.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_sourceMaskCycleAction_zero ends m j k l zero p c z

/--
[sourceMaskCycleAction_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sourceMaskCycleAction_involutive_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {z : sourceMaskCycleSpace ends p}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  sourceMaskCycleAction ends m j k l zero p (sourceMaskCycleAction ends m j k l zero p c z) z = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sourceMaskCycleAction_involutive ends m j k l zero p z c

/--
[cycleTranslation_pairBalance_nonneg_of_coversNegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma cycleTranslation_pairBalance_nonneg_of_coversNegative_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {z : sourceMaskCycleSpace ends p}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcovers : CycleTranslationCoversNegative ends m j k l zero p z) :
-- imply
  0 ≤ reversalGateBalance ends m j k l zero p c + reversalGateBalance ends m j k l zero p (sourceMaskCycleAction ends m j k l zero p c z) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.cycleTranslation_pairBalance_nonneg_of_coversNegative ends m j k l zero p z hcovers c

/--
[sum_reversalGateBalance_eq_cycleCutCorrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sum_reversalGateBalance_eq_cycleCutCorrelation_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c₀ : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (∑ c : leftSourceMaskFiber ends m j k l zero p, reversalGateBalance ends m j k l zero p c) = ∑ z : sourceMaskCycleSpace ends p, (bipartitionDisconnectIndicator ends m ((rowClass m c₀.1 0 ∆ (z.1.1 ∪ z.2.1)) ∆ p.1) k zero - bipartitionDisconnectIndicator ends m (rowClass m c₀.1 0 ∆ (z.1.1 ∪ z.2.1)) k zero) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sum_reversalGateBalance_eq_cycleCutCorrelation ends m j k l zero p c₀

/--
[sum_reversalGateBalance_eq_card_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sum_reversalGateBalance_eq_card_sub_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (∑ c : leftSourceMaskFiber ends m j k l zero p, reversalGateBalance ends m j k l zero p c) = (Fintype.card (reversedRightSourceMaskGateFiber ends m j k l zero p) : ℤ) - Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sum_reversalGateBalance_eq_card_sub ends m j k l zero p

/--
[sum_reversalGateBalance_nonneg_of_equivPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sum_reversalGateBalance_nonneg_of_equivPairs_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {e : leftSourceMaskFiber ends m j k l zero p ≃ leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p, 0 ≤ reversalGateBalance ends m j k l zero p c + reversalGateBalance ends m j k l zero p (e c)) :
-- imply
  0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p, reversalGateBalance ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sum_reversalGateBalance_nonneg_of_equivPairs ends m j k l zero p e hpairs

/--
[sum_reversalGateBalance_nonneg_of_cycleTranslationPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sum_reversalGateBalance_nonneg_of_cycleTranslationPairs_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {X Y : Finset I}
-- given
  (ends : I -> Sym2 W)
  (hX : X ⊆ p.1)
  (hY : Y ⊆ p.2)
  (hsrcX : sources ends X = ∅)
  (hsrcY : sources ends Y = ∅)
  (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p, 0 ≤ reversalGateBalance ends m j k l zero p c + reversalGateBalance ends m j k l zero p (sourceMaskCycleTranslationEquiv ends m j k l zero p X Y hX hY hsrcX hsrcY c)) :
-- imply
  0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p, reversalGateBalance ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sum_reversalGateBalance_nonneg_of_cycleTranslationPairs ends m j k l zero p X Y hX hY hsrcX hsrcY hpairs

/--
[sum_reversalGateBalance_nonneg_of_exists_cycleTranslationCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sum_reversalGateBalance_nonneg_of_exists_cycleTranslationCover_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hcover : ∃ z : sourceMaskCycleSpace ends p, CycleTranslationCoversNegative ends m j k l zero p z) :
-- imply
  0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p, reversalGateBalance ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sum_reversalGateBalance_nonneg_of_exists_cycleTranslationCover ends m j k l zero p hcover

/--
[sum_reversalGateBalance_nonneg_of_outerCyclePairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma sum_reversalGateBalance_nonneg_of_outerCyclePairs_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {Y : Finset I}
-- given
  (ends : I -> Sym2 W)
  (hY : Y ⊆ p.2)
  (hsrcY : sources ends Y = ∅)
  (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p, 0 ≤ reversalGateBalance ends m j k l zero p c + reversalGateBalance ends m j k l zero p (outerCycleSourceMaskEquiv ends m j k l zero p Y hY hsrcY c)) :
-- imply
  0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p, reversalGateBalance ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sum_reversalGateBalance_nonneg_of_outerCyclePairs ends m j k l zero p Y hY hsrcY hpairs

/--
[canonicalReferenceReturnRaw_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalReferenceReturnRaw_involutive_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r c : ↑m -> Fin 4) :
-- imply
  canonicalReferenceReturnRaw ends m k zero r (canonicalReferenceReturnRaw ends m k zero r c) = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalReferenceReturnRaw_involutive ends m k zero r c

/--
[canonicalReferenceReturnRaw_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalReferenceReturnRaw_eq_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r c d : ↑m -> Fin 4) :
-- imply
  canonicalReferenceReturnRaw ends m k zero r c = d ↔ canonicalReferenceReturnRaw ends m k zero r d = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalReferenceReturnRaw_eq_iff ends m k zero r c d

/--
[canonicalSelfPulledSourcePoint_val_eq_referenceReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalSelfPulledSourcePoint_val_eq_referenceReturn_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hdisc : RowsDisconnect ends m c.1 k zero) :
-- imply
  (canonicalSelfPulledSourcePoint ends m j k l zero hloop hjk hkl hk0 p c hdisc).1 = canonicalReferenceReturnRaw ends m k zero c.1 c.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfPulledSourcePoint_val_eq_referenceReturn ends m j k l zero hloop hjk hkl hk0 p c hdisc

/--
[canonicalSelfPulledSourcePoint_reference_fails_of_negative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalSelfPulledSourcePoint_reference_fails_of_negative_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hneg : ReversalGateNegative ends m j k l zero p c) :
-- imply
  ¬ CanonicalTransferWorks ends m k zero c.1 (canonicalSelfPulledSourcePoint ends m j k l zero hloop hjk hkl hk0 p c hneg.1).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfPulledSourcePoint_reference_fails_of_negative ends m j k l zero hloop hjk hkl hk0 p c hneg

/--
[canonicalSelfPulledSourcePoint_rightGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalSelfPulledSourcePoint_rightGate_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hdisc : RowsDisconnect ends m c.1 k zero) :
-- imply
  RowsDisconnect ends m (middleSwap m (canonicalSelfPulledSourcePoint ends m j k l zero hloop hjk hkl hk0 p c hdisc).1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfPulledSourcePoint_rightGate ends m j k l zero hloop hjk hkl hk0 p c hdisc

/--
[canonicalSelfPullbackCycleCandidate_maps_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalSelfPullbackCycleCandidate_maps_base_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hdisc : RowsDisconnect ends m c.1 k zero) :
-- imply
  sourceMaskCycleAction ends m j k l zero p c (canonicalSelfPullbackCycleCandidate ends m j k l zero hloop hjk hkl hk0 p c hdisc) = canonicalSelfPulledSourcePoint ends m j k l zero hloop hjk hkl hk0 p c hdisc := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfPullbackCycleCandidate_maps_base ends m j k l zero hloop hjk hkl hk0 p c hdisc

/--
[canonicalRawCommonClosureIter_subset_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalRawCommonClosureIter_subset_succ_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {n : Nat}
-- given
  (ends : I -> Sym2 W) :
-- imply
  canonicalRawCommonClosureIter ends m j k l zero p n ⊆ canonicalRawCommonClosureIter ends m j k l zero p (n + 1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRawCommonClosureIter_subset_succ ends m j k l zero p n

/--
[exists_canonicalRawCommonClosureIter_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma exists_canonicalRawCommonClosureIter_fixed_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  ∃ n ≤ Fintype.card (leftSourceMaskFiber ends m j k l zero p) - (canonicalRawNegativeGateFinset ends m j k l zero p).card, canonicalRawCommonClosureIter ends m j k l zero p (n + 1) = canonicalRawCommonClosureIter ends m j k l zero p n := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalRawCommonClosureIter_fixed ends m j k l zero p

/--
[canonicalRawCommonClosure_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalRawCommonClosure_fixed_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  StatMech.FrontierA.finiteCommonClosureStep (fun c : leftSourceMaskFiber ends m j k l zero p => RowsDisconnect ends m c.1 k zero) (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero) (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p) = canonicalRawCommonClosure ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRawCommonClosure_fixed ends m j k l zero p

/--
[canonicalRawNegativeGateFinset_subset_commonClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalRawNegativeGateFinset_subset_commonClosure_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  canonicalRawNegativeGateFinset ends m j k l zero p ⊆ canonicalRawCommonClosure ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRawNegativeGateFinset_subset_commonClosure ends m j k l zero p

/--
[canonicalRawCommonClosure_leftGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalRawCommonClosure_leftGate_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  ∀ c ∈ canonicalRawCommonClosure ends m j k l zero p, RowsDisconnect ends m c.1 k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRawCommonClosure_leftGate ends m j k l zero p

/--
[canonicalRawCommonClosure_common_mem_neighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalRawCommonClosure_common_mem_neighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hc : c ∈ canonicalRawCommonClosure ends m j k l zero p)
  (hcRight : RowsDisconnect ends m (middleSwap m c.1) k zero) :
-- imply
  c ∈ StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRawCommonClosure_common_mem_neighborhood ends m j k l zero p c hc hcRight

/--
[canonicalRawCommonClosure_right_iff_neighborhood_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalRawCommonClosure_right_iff_neighborhood_left_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (c ∈ canonicalRawCommonClosure ends m j k l zero p ∧ RowsDisconnect ends m (middleSwap m c.1) k zero) ↔ (c ∈ StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p) ∧ RowsDisconnect ends m c.1 k zero) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRawCommonClosure_right_iff_neighborhood_left ends m j k l zero p c

/--
[card_canonicalNegativeFullNeighborhood_eq_parts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_canonicalNegativeFullNeighborhood_eq_parts_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (negativeReversalGateFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (canonicalNegativeFullNeighborhood ends m j k l zero p S).card = (canonicalNegativePositiveNeighborhood ends m j k l zero p S).card + (canonicalNegativeCommonNeighborhood ends m j k l zero p S).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_canonicalNegativeFullNeighborhood_eq_parts ends m j k l zero p S

/--
[positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (negativeReversalGateFiber ends m j k l zero p)}
  {q : positiveReversalGateFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  positiveReversalGateToRightMaskFiber ends m j k l zero p q ∈ canonicalNegativePositiveNeighborhood ends m j k l zero p S ↔ ∃ c ∈ S, CanonicalDiscrepancyRelated ends m j k l zero p c q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff ends m j k l zero p S q

/--
[image_canonicalDiscrepancyNeighborhood_eq_positiveNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma image_canonicalDiscrepancyNeighborhood_eq_positiveNeighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (negativeReversalGateFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W) :
-- imply
  transportedCanonicalDiscrepancyNeighborhood ends m j k l zero p S = canonicalNegativePositiveNeighborhood ends m j k l zero p S := by
-- proof
  apply StatMech.GrahamGHS.FourColor.image_canonicalDiscrepancyNeighborhood_eq_positiveNeighborhood ends m j k l zero p S

/--
[card_canonicalNegativePositiveNeighborhood_eq_discrepancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_canonicalNegativePositiveNeighborhood_eq_discrepancy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (negativeReversalGateFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (canonicalNegativePositiveNeighborhood ends m j k l zero p S).card = (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_canonicalNegativePositiveNeighborhood_eq_discrepancy ends m j k l zero p S

/--
[card_canonicalNegativeFullNeighborhood_eq_discrepancy_add_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_canonicalNegativeFullNeighborhood_eq_discrepancy_add_common_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (negativeReversalGateFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (canonicalNegativeFullNeighborhood ends m j k l zero p S).card = (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card + (canonicalNegativeCommonNeighborhood ends m j k l zero p S).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_canonicalNegativeFullNeighborhood_eq_discrepancy_add_common ends m j k l zero p S

/--
[canonicalDiscrepancyCommonCompensatedExpansion_iff_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalDiscrepancyCommonCompensatedExpansion_iff_hall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalDiscrepancyCommonCompensatedExpansion ends m j k l zero p ↔ CanonicalDiscrepancyHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalDiscrepancyCommonCompensatedExpansion_iff_hall ends m j k l zero p

/--
[canonicalDiscrepancyTargetSelector_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalDiscrepancyTargetSelector_related_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : negativeReversalGateFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hsingle : CanonicalDiscrepancySingletonExpansion ends m j k l zero p) :
-- imply
  CanonicalDiscrepancyRelated ends m j k l zero p c (canonicalDiscrepancyTargetSelector ends m j k l zero p hsingle c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalDiscrepancyTargetSelector_related ends m j k l zero p hsingle c

/--
[canonicalDiscrepancyReferenceSelector_works](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalDiscrepancyReferenceSelector_works_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : negativeReversalGateFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hsingle : CanonicalDiscrepancySingletonExpansion ends m j k l zero p) :
-- imply
  CanonicalTransferWorks ends m k zero (canonicalDiscrepancyReferenceSelector ends m j k l zero p hsingle c).1.1 (negativeReversalGateToLeftMaskFiber ends m j k l zero p c).1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalDiscrepancyReferenceSelector_works ends m j k l zero p hsingle c

/--
[card_le_canonicalDiscrepancyNeighborhood_of_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_le_canonicalDiscrepancyNeighborhood_of_card_le_one_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (negativeReversalGateFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hsingle : CanonicalDiscrepancySingletonExpansion ends m j k l zero p)
  (hcard : S.card ≤ 1) :
-- imply
  S.card ≤ (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalDiscrepancyNeighborhood_of_card_le_one ends m j k l zero p hsingle S hcard

/--
[canonicalDiscrepancyHall_iff_exists_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalDiscrepancyHall_iff_exists_matching_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalDiscrepancyHall ends m j k l zero p ↔ ∃ f : negativeReversalGateFiber ends m j k l zero p ↪ positiveReversalGateFiber ends m j k l zero p, ∀ c, CanonicalDiscrepancyRelated ends m j k l zero p c (f c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalDiscrepancyHall_iff_exists_matching ends m j k l zero p

/--
[card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) ↔ Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) ≤ Fintype.card (reversedRightSourceMaskGateFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates ends m j k l zero p

/--
[card_leftMaskFiber_le_rightMaskFiber_iff_discrepancies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_iff_discrepancies_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) ↔ Fintype.card (negativeReversalGateFiber ends m j k l zero p) ≤ Fintype.card (positiveReversalGateFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_iff_discrepancies ends m j k l zero p

/--
[card_leftMaskFiber_le_rightMaskFiber_of_commonClosedRawExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_commonClosedRawExpansion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {T : Finset (leftSourceMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hnegative : canonicalRawNegativeGateFinset ends m j k l zero p ⊆ T)
  (hleft : ∀ c ∈ T, RowsDisconnect ends m c.1 k zero)
  (hclosed : StatMech.FrontierA.finiteCommonClosureStep (fun c : leftSourceMaskFiber ends m j k l zero p => RowsDisconnect ends m c.1 k zero) (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero) (CanonicalRawGateRelated ends m j k l zero p) T = T)
  (hexpand : T.card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) T).card) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_commonClosedRawExpansion ends m j k l zero p T hnegative hleft hclosed hexpand

/--
[card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hexpand : (canonicalRawCommonClosure ends m j k l zero p).card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p)).card) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion ends m j k l zero p hexpand

/--
[canonicalStableRawCollisionSurplus_iff_expands](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawCollisionSurplus_iff_expands_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalStableRawCollisionSurplus ends m j k l zero p ↔ (canonicalRawCommonClosure ends m j k l zero p).card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawCollisionSurplus_iff_expands ends m j k l zero p

/--
[canonicalStableRawSelfBase_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawSelfBase_related_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : ↑(canonicalRawCommonClosure ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  CanonicalRawGateRelated ends m j k l zero p c.1 (canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfBase_related ends m j k l zero hloop hjk hkl hk0 p c

/--
[canonicalStableRawRightBase_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawRightBase_mem_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W) :
-- imply
  canonicalStableRawRightBase ends m j k l zero p d ∈ canonicalRawCommonClosure ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawRightBase_mem ends m j k l zero p d

/--
[canonicalStableRawRightBase_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawRightBase_related_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalRawGateRelated ends m j k l zero p (canonicalStableRawRightBase ends m j k l zero p d) d.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawRightBase_related ends m j k l zero p d

/--
[canonicalStableRawSelfPreimageFinset_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawSelfPreimageFinset_nonempty_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : ∃ c : ↑(canonicalRawCommonClosure ends m j k l zero p), canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = d.1) :
-- imply
  (canonicalStableRawSelfPreimageFinset ends m j k l zero hloop hjk hkl hk0 p d).Nonempty := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfPreimageFinset_nonempty ends m j k l zero hloop hjk hkl hk0 p d hself

/--
[canonicalStableRawPreferredSelfPreimage_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawPreferredSelfPreimage_spec_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : ∃ c : ↑(canonicalRawCommonClosure ends m j k l zero p), canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = d.1) :
-- imply
  canonicalStableRawPreferredSelfPreimage ends m j k l zero hloop hjk hkl hk0 p d hself ∈ canonicalStableRawSelfPreimageFinset ends m j k l zero hloop hjk hkl hk0 p d ∧ ∀ c ∈ canonicalStableRawSelfPreimageFinset ends m j k l zero hloop hjk hkl hk0 p d, canonicalStableRawSourceRank ends m j k l zero p (canonicalStableRawPreferredSelfPreimage ends m j k l zero hloop hjk hkl hk0 p d hself) ≤ canonicalStableRawSourceRank ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredSelfPreimage_spec ends m j k l zero hloop hjk hkl hk0 p d hself

/--
[canonicalStableRawPreferredRightBase_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawPreferredRightBase_mem_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d ∈ canonicalRawCommonClosure ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p d

/--
[canonicalStableRawPreferredRightBase_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawPreferredRightBase_related_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  CanonicalRawGateRelated ends m j k l zero p (canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d) d.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredRightBase_related ends m j k l zero hloop hjk hkl hk0 p d

/--
[canonicalStableRawPreferredRightBase_self_eq_of_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawPreferredRightBase_self_eq_of_exists_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : ∃ c : ↑(canonicalRawCommonClosure ends m j k l zero p), canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = d.1) :
-- imply
  canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p d⟩ = d.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredRightBase_self_eq_of_exists ends m j k l zero hloop hjk hkl hk0 p d hself

/--
[canonicalStableRawPreferredRightBase_rank_lt_of_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalStableRawPreferredRightBase_rank_lt_of_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
  {c : ↑(canonicalRawCommonClosure ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = d.1)
  (hne : c.1 ≠ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d) :
-- imply
  canonicalStableRawSourceRank ends m j k l zero p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p d⟩ < canonicalStableRawSourceRank ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredRightBase_rank_lt_of_self ends m j k l zero hloop hjk hkl hk0 p d c hself hne

/--
[exists_canonicalRawGateRelated_ne_self_of_exceptionalSelfToken](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma exists_canonicalRawGateRelated_ne_self_of_exceptionalSelfToken_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : ↑(canonicalRawCommonClosure ends m j k l zero p)}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = d.1)
  (hne : c.1 ≠ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d) :
-- imply
  ∃ e : leftSourceMaskFiber ends m j k l zero p, CanonicalRawGateRelated ends m j k l zero p c.1 e ∧ e ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalRawGateRelated_ne_self_of_exceptionalSelfToken ends m j k l zero hloop hjk hkl hk0 p c d hself hne

/--
[canonicalRawCommonClosure_expands_of_collisionTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalRawCommonClosure_expands_of_collisionTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hemb : CanonicalStableRawCollisionTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (canonicalRawCommonClosure ends m j k l zero p).card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRawCommonClosure_expands_of_collisionTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hemb

/--
[card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hemb : CanonicalStableRawCollisionTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hemb

/--
[canonicalRawCommonClosure_expands_of_collisionSurplus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma canonicalRawCommonClosure_expands_of_collisionSurplus_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hsurplus : CanonicalStableRawCollisionSurplus ends m j k l zero p) :
-- imply
  (canonicalRawCommonClosure ends m j k l zero p).card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRawCommonClosure_expands_of_collisionSurplus ends m j k l zero p hsurplus

/--
[card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionSurplus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionSurplus_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hsurplus : CanonicalStableRawCollisionSurplus ends m j k l zero p) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionSurplus ends m j k l zero p hsurplus

/--
[card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) ↔ 0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p, reversalGateBalance ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance ends m j k l zero p

/--
[card_leftMaskFiber_le_rightMaskFiber_of_canonicalDiscrepancyHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_canonicalDiscrepancyHall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hhall : CanonicalDiscrepancyHall ends m j k l zero p) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_canonicalDiscrepancyHall ends m j k l zero p hhall

/--
[card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslationPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslationPairs_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {X Y : Finset I}
-- given
  (ends : I -> Sym2 W)
  (hX : X ⊆ p.1)
  (hY : Y ⊆ p.2)
  (hsrcX : sources ends X = ∅)
  (hsrcY : sources ends Y = ∅)
  (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p, 0 ≤ reversalGateBalance ends m j k l zero p c + reversalGateBalance ends m j k l zero p (sourceMaskCycleTranslationEquiv ends m j k l zero p X Y hX hY hsrcX hsrcY c)) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslationPairs ends m j k l zero p X Y hX hY hsrcX hsrcY hpairs

/--
[card_leftMaskFiber_le_rightMaskFiber_of_exists_cycleTranslationCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_exists_cycleTranslationCover_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hcover : ∃ z : sourceMaskCycleSpace ends p, CycleTranslationCoversNegative ends m j k l zero p z) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_exists_cycleTranslationCover ends m j k l zero p hcover

/--
[card_leftMaskFiber_le_rightMaskFiber_of_outerCyclePairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_outerCyclePairs_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {Y : Finset I}
-- given
  (ends : I -> Sym2 W)
  (hY : Y ⊆ p.2)
  (hsrcY : sources ends Y = ∅)
  (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p, 0 ≤ reversalGateBalance ends m j k l zero p c + reversalGateBalance ends m j k l zero p (outerCycleSourceMaskEquiv ends m j k l zero p Y hY hsrcY c)) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_outerCyclePairs ends m j k l zero p Y hY hsrcY hpairs


-- created on 2026-10-23
