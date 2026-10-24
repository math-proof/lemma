import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[embedding_surjective_of_card_le_two_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma embedding_surjective_of_card_le_two_of_ne_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [Fintype B]
  {f : A ↪ B}
  {a b : A}
-- given
  (hab : a ≠ b)
  (hB : Fintype.card B ≤ 2) :
-- imply
  Function.Surjective f := by
-- proof
  apply StatMech.GrahamGHS.FourColor.embedding_surjective_of_card_le_two_of_ne f a b hab hB

/--
[eq_of_middle_outer_colorClass_two_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma eq_of_middle_outer_colorClass_two_three_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (c d : ↑m -> Fin 4)
  (hmid : middleMask m c = middleMask m d)
  (hout : outerMask m c = outerMask m d)
  (htwo : colorClass m c 2 = colorClass m d 2)
  (hthree : colorClass m c 3 = colorClass m d 3) :
-- imply
  c = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.eq_of_middle_outer_colorClass_two_three m c d hmid hout htwo hthree

/--
[leftMaskCycleEmbedding_surjective_of_cycleProduct_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma leftMaskCycleEmbedding_surjective_of_cycleProduct_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hcd : c ≠ d)
  (hcycle : Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  Function.Surjective (leftMaskCycleEmbedding ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftMaskCycleEmbedding_surjective_of_cycleProduct_le_two ends m j k l zero p c d hcd hcycle

/--
[exists_leftMaskFiber_emptyCyclePair_of_cycleProduct_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma exists_leftMaskFiber_emptyCyclePair_of_cycleProduct_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hcd : c ≠ d)
  (hcycle : Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  ∃ e : leftMaskFiber ends m j k l zero p, leftMaskCyclePair ends m j k l zero p e = emptyMaskCyclePair ends p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_leftMaskFiber_emptyCyclePair_of_cycleProduct_le_two ends m j k l zero p c d hcd hcycle

/--
[cycleProduct_le_two_factor_card_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma cycleProduct_le_two_factor_card_eq_one_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {p : Finset I × Finset I}
-- given
  (hcycle : Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  Fintype.card (boundarySector ends p.1 ∅) = 1 ∨ Fintype.card (boundarySector ends p.2 ∅) = 1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.cycleProduct_le_two_factor_card_eq_one ends p hcycle

/--
[colorClass_zero_eq_outerMask_sdiff_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma colorClass_zero_eq_outerMask_sdiff_three_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {c : ↑m → Fin 4} :
-- imply
  colorClass m c 0 = outerMask m c \ colorClass m c 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_zero_eq_outerMask_sdiff_three m c

/--
[leftMaskCycleDifference_empty_side_of_cycleProduct_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma leftMaskCycleDifference_empty_side_of_cycleProduct_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hcycle : Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  balancedMiddleDifference m c.1.1 d.1.1 = ∅ ∨ balancedOuterDifference m c.1.1 d.1.1 = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftMaskCycleDifference_empty_side_of_cycleProduct_le_two ends m j k l zero p c d hcycle

/--
[rows_eq_masks_of_leftMaskCyclePair_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma rows_eq_masks_of_leftMaskCyclePair_eq_empty_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (hc : leftMaskCyclePair ends m j k l zero p c = emptyMaskCyclePair ends p) :
-- imply
  rowClass m c.1.1 0 = p.2 ∧ rowClass m c.1.1 1 = p.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rows_eq_masks_of_leftMaskCyclePair_eq_empty ends m j k l zero p c hc

/--
[exists_leftMaskFiber_with_disconnected_masks_of_cycleProduct_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma exists_leftMaskFiber_with_disconnected_masks_of_cycleProduct_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hcd : c ≠ d)
  (hcycle : Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  ∃ e : leftMaskFiber ends m j k l zero p, ¬ connK ends p.1 k zero ∧ ¬ connK ends p.2 k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_leftMaskFiber_with_disconnected_masks_of_cycleProduct_le_two ends m j k l zero p c d hcd hcycle

/--
[rightPattern_of_sourceless_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma rightPattern_of_sourceless_balancedSwap_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m X Y : Finset I}
  {A B : Finset W}
  {u v : W}
  {c : ↑m → Fin 4}
-- given
  (hright : RightPattern ends m A B u v c)
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
  (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
  (hsrcX : sources ends X = ∅)
  (hsrcY : sources ends Y = ∅)
  (hdisc : RowsDisconnect ends m (balancedSwap m X Y c) u v) :
-- imply
  RightPattern ends m A B u v (balancedSwap m X Y c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightPattern_of_sourceless_balancedSwap hright hX hY hsrcX hsrcY hdisc

/--
[rightMaskCycleTranslate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_ne_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {c d q : ↑m → Fin 4}
-- given
  (hmidcd : middleMask m c = middleMask m d)
  (houtcd : outerMask m c = outerMask m d)
  (hmidcq : middleMask m c = middleMask m q)
  (houtcq : outerMask m c = outerMask m q)
  (hcd : c ≠ d) :
-- imply
  rightMaskCycleTranslate m c d q ≠ q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_ne m c d q hmidcd houtcd hmidcq houtcq hcd

/--
[exists_rightMaskFiber_pair_of_cycleTranslate_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma exists_rightMaskFiber_pair_of_cycleTranslate_disconnects_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (hcd : c ≠ d)
  (hdisc : RowsDisconnect ends m (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero) :
-- imply
  ∃ q r : rightMaskFiber ends m j k l zero p, q ≠ r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_rightMaskFiber_pair_of_cycleTranslate_disconnects ends m j k l zero p c d hcd q hdisc

/--
[leftMaskFiber_card_le_cycleProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma leftMaskFiber_card_le_cycleProduct_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftMaskFiber_card_le_cycleProduct ends m j k l zero p

/--
[rightMaskFiber_card_le_cycleProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma rightMaskFiber_card_le_cycleProduct_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Fintype.card (rightMaskFiber ends m j k l zero p) ≤ Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskFiber_card_le_cycleProduct ends m j k l zero p

/--
[rowDataRepairHall_of_cycleProduct_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma rowDataRepairHall_of_cycleProduct_le_one_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcycle : forall p : Finset I × Finset I, Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 1) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_cycleProduct_le_one ends m j k l zero hloop hjk hkl hk0 hcycle

/--
[rowDataRepairHall_of_cycleProduct_le_two_of_rightPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean)
-/
@[path]
private lemma rowDataRepairHall_of_cycleProduct_le_two_of_rightPairs_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcycle : forall p : Finset I × Finset I, Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2)
  (hpair : forall (p : Finset I × Finset I) (c d : leftMaskFiber ends m j k l zero p), c ≠ d -> ∃ q r : rightMaskFiber ends m j k l zero p, q ≠ r) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_cycleProduct_le_two_of_rightPairs ends m j k l zero hloop hjk hkl hk0 hcycle hpair


-- created on 2026-10-23
