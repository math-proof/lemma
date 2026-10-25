import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall.Part5
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[rightMaskCycleTranslate_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_trans_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (a b c q : ↑m -> Fin 4) :
-- imply
  rightMaskCycleTranslate m b c (rightMaskCycleTranslate m a b q) = rightMaskCycleTranslate m a c q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_trans m a b c q

/--
[rightMaskCycleTranslate_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (a q : ↑m -> Fin 4) :
-- imply
  rightMaskCycleTranslate m a a q = q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_self m a q

/--
[rightMaskCycleTranslate_left_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_left_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (a q : ↑m -> Fin 4)
  (ha : fourColorMaskProfile m a = fourColorMaskProfile m q) :
-- imply
  Function.Injective (fun c : {c : ↑m -> Fin 4 // fourColorMaskProfile m c = fourColorMaskProfile m a} => rightMaskCycleTranslate m a c.1 q) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_left_injective m a q ha

/--
[rightMaskCycleTranslate_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_rows_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (a c q : ↑m -> Fin 4)
  (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
  (haq : fourColorMaskProfile m a = fourColorMaskProfile m q) :
-- imply
  rowClass m (rightMaskCycleTranslate m a c q) 0 = rowClass m q 0 ∆ rightMaskCycleDifference m a c ∧ rowClass m (rightMaskCycleTranslate m a c q) 1 = rowClass m q 1 ∆ rightMaskCycleDifference m a c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_rows m a c q hac haq

/--
[not_conn_symmDiff_of_noCrossing_componentComplement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma not_conn_symmDiff_of_noCrossing_componentComplement_eq
  [Fintype I]
  [DecidableEq I]
  {K D : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (hdisc : ¬ connK ends K k zero)
  (hcross : NoCrossingK ends (K ∆ D) (StatMech.FrontierA.grahamComponentComplement ends K k)) :
-- imply
  ¬ connK ends (K ∆ D) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.not_conn_symmDiff_of_noCrossing_componentComplement ends K D k zero hdisc hcross

/--
[exists_mem_difference_crossing_of_toggle_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma exists_mem_difference_crossing_of_toggle_connected_eq
  [Fintype I]
  [DecidableEq I]
  {K D : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (hdisc : ¬ connK ends K k zero)
  (hconn : connK ends (K ∆ D) k zero) :
-- imply
  ∃ e ∈ D, CrossesRootComponentCut ends K k e := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_mem_difference_crossing_of_toggle_connected ends K D k zero hdisc hconn

/--
[exists_cycleDifference_crossing_of_translate_not_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma exists_cycleDifference_crossing_of_translate_not_disconnects_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a c q : ↑m -> Fin 4)
  (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
  (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
  (hq : RowsDisconnect ends m q k zero)
  (hfail : ¬ RowsDisconnect ends m (rightMaskCycleTranslate m a c q) k zero) :
-- imply
  (∃ e ∈ rightMaskCycleDifference m a c, CrossesRootComponentCut ends (rowClass m q 0) k e) ∨ ∃ e ∈ rightMaskCycleDifference m a c, CrossesRootComponentCut ends (rowClass m q 1) k e := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_cycleDifference_crossing_of_translate_not_disconnects ends m k zero a c q hac haq hq hfail

/--
[rightMaskCycleTranslate_disconnects_of_no_crossing_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_disconnects_of_no_crossing_edges_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a c q : ↑m -> Fin 4)
  (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
  (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
  (hq : RowsDisconnect ends m q k zero)
  (hno0 : ∀ e ∈ rightMaskCycleDifference m a c, ¬ CrossesRootComponentCut ends (rowClass m q 0) k e)
  (hno1 : ∀ e ∈ rightMaskCycleDifference m a c, ¬ CrossesRootComponentCut ends (rowClass m q 1) k e) :
-- imply
  RowsDisconnect ends m (rightMaskCycleTranslate m a c q) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_disconnects_of_no_crossing_edges ends m k zero a c q hac haq hq hno0 hno1

/--
[rightMaskCycleTranslate_disconnects_of_respectsCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_disconnects_of_respectsCuts_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a c q : ↑m -> Fin 4)
  (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
  (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
  (hq : RowsDisconnect ends m q k zero)
  (hcuts : RightMaskCycleDifferenceRespectsCuts ends m (rowClass m q 0) (rightMaskCycleDifference m a c) k) :
-- imply
  RowsDisconnect ends m (rightMaskCycleTranslate m a c q) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_disconnects_of_respectsCuts ends m k zero a c q hac haq hq hcuts

/--
[card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hgate : ∀ c : leftMaskFiber ends m j k l zero p, RowsDisconnect ends m (rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1) k zero) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate ends m j k l zero p a q hgate

/--
[cycleTranslateBadCount_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma cycleTranslateBadCount_eq_zero_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {base : leftMaskFiber ends m j k l zero p × rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  cycleTranslateBadCount ends m j k l zero p base = 0 ↔ ∀ c : leftMaskFiber ends m j k l zero p, RowsDisconnect ends m (rightMaskCycleTranslate m base.1.1.1 c.1.1 base.2.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.cycleTranslateBadCount_eq_zero_iff ends m j k l zero p base

/--
[cycleTranslateMinBadPair_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma cycleTranslateMinBadPair_spec_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  ∀ base : leftMaskFiber ends m j k l zero p × rightMaskFiber ends m j k l zero p, cycleTranslateBadCount ends m j k l zero p (cycleTranslateMinBadPair ends m j k l zero hloop hjk hkl hk0 p c) ≤ cycleTranslateBadCount ends m j k l zero p base := by
-- proof
  apply StatMech.GrahamGHS.FourColor.cycleTranslateMinBadPair_spec ends m j k l zero hloop hjk hkl hk0 p c

/--
[card_leftMaskFiber_le_rightMaskFiber_of_minBadCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma card_leftMaskFiber_le_rightMaskFiber_of_minBadCount_zero_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hzero : cycleTranslateBadCount ends m j k l zero p (cycleTranslateMinBadPair ends m j k l zero hloop hjk hkl hk0 p c) = 0) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftMaskFiber_le_rightMaskFiber_of_minBadCount_zero ends m j k l zero hloop hjk hkl hk0 p c hzero

/--
[rowDataRepairHall_of_cycleTranslate_orbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_cycleTranslate_orbits_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (horbit : ∀ p : Finset I × Finset I, Nonempty (leftMaskFiber ends m j k l zero p) -> ∃ a : leftMaskFiber ends m j k l zero p, ∃ q : rightMaskFiber ends m j k l zero p, ∀ c : leftMaskFiber ends m j k l zero p, RowsDisconnect ends m (rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1) k zero) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_cycleTranslate_orbits ends m j k l zero horbit

/--
[rowDataRepairHall_of_minCycleTranslateBadCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_minCycleTranslateBadCount_zero_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hzero : ∀ (p : Finset I × Finset I) (c : leftMaskFiber ends m j k l zero p), cycleTranslateBadCount ends m j k l zero p (cycleTranslateMinBadPair ends m j k l zero hloop hjk hkl hk0 p c) = 0) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_minCycleTranslateBadCount_zero ends m j k l zero hloop hjk hkl hk0 hzero

/--
[rowDataRepairHall_of_cycleTranslate_respectsCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_cycleTranslate_respectsCuts_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hcuts : ∀ p : Finset I × Finset I, Nonempty (leftMaskFiber ends m j k l zero p) -> ∃ a : leftMaskFiber ends m j k l zero p, ∃ q : rightMaskFiber ends m j k l zero p, ∀ c : leftMaskFiber ends m j k l zero p, RightMaskCycleDifferenceRespectsCuts ends m (rowClass m q.1.1 0) (rightMaskCycleDifference m a.1.1 c.1.1) k) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_cycleTranslate_respectsCuts ends m j k l zero hcuts

/--
[rowDataRepairHall_of_cycleTranslate_no_crossing_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_cycleTranslate_no_crossing_edges_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hno : ∀ p : Finset I × Finset I, Nonempty (leftMaskFiber ends m j k l zero p) -> ∃ a : leftMaskFiber ends m j k l zero p, ∃ q : rightMaskFiber ends m j k l zero p, ∀ c : leftMaskFiber ends m j k l zero p, (∀ e ∈ rightMaskCycleDifference m a.1.1 c.1.1, ¬ CrossesRootComponentCut ends (rowClass m q.1.1 0) k e) ∧ ∀ e ∈ rightMaskCycleDifference m a.1.1 c.1.1, ¬ CrossesRootComponentCut ends (rowClass m q.1.1 1) k e) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_cycleTranslate_no_crossing_edges ends m j k l zero hno


-- created on 2026-10-23
