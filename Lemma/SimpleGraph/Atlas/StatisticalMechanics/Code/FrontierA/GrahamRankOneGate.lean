import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamRankOneGate
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[eq_or_eq_of_card_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma eq_or_eq_of_card_le_two_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [DecidableEq A]
  {a b x : A}
-- given
  (hab : a ≠ b)
  (hcard : Fintype.card A ≤ 2) :
-- imply
  x = a ∨ x = b := by
-- proof
  apply StatMech.GrahamGHS.FourColor.eq_or_eq_of_card_le_two a b x hab hcard

/--
[rootSpanning_of_subsingleton_cycleSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rootSpanning_of_subsingleton_cycleSector_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {S : Finset I}
  {a b : W}
-- given
  (hloop : ∀ i ∈ S, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hsrc : sources ends S = {a, b})
  (hsub : Subsingleton (boundarySector ends S ∅)) :
-- imply
  RootSpanning ends S a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rootSpanning_of_subsingleton_cycleSector ends S a b hloop hab hsrc hsub

/--
[subsingleton_cycleSector_sdiff_of_card_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma subsingleton_cycleSector_sdiff_of_card_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {S Z : Finset I}
-- given
  (hZS : Z ⊆ S)
  (hZsrc : sources ends Z = ∅)
  (hZne : Z ≠ ∅)
  (hcard : Fintype.card (boundarySector ends S ∅) ≤ 2) :
-- imply
  Subsingleton (boundarySector ends (S \ Z) ∅) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.subsingleton_cycleSector_sdiff_of_card_le_two ends S Z hZS hZsrc hZne hcard

/--
[rootSpanning_sdiff_of_cycleSector_card_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rootSpanning_sdiff_of_cycleSector_card_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {S Z : Finset I}
  {a b : W}
-- given
  (hloop : ∀ i ∈ S, ¬ (ends i).IsDiag)
  (hab : a ≠ b)
  (hsrc : sources ends S = {a, b})
  (hZS : Z ⊆ S)
  (hZsrc : sources ends Z = ∅)
  (hZne : Z ≠ ∅)
  (hcard : Fintype.card (boundarySector ends S ∅) ≤ 2) :
-- imply
  RootSpanning ends (S \ Z) a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rootSpanning_sdiff_of_cycleSector_card_le_two ends S Z a b hloop hab hsrc hZS hZsrc hZne hcard

/--
[conn_union_union_cycle_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma conn_union_union_cycle_side_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {K L Z : Finset I}
  {k x : W}
-- given
  (hK : RootSpanning ends K k)
  (hL : RootSpanning ends L k)
  (hconn : connK ends ((K ∪ L) ∪ Z) k x) :
-- imply
  connK ends (K ∪ Z) k x ∨ connK ends (L ∪ Z) k x := by
-- proof
  apply StatMech.GrahamGHS.FourColor.conn_union_union_cycle_side ends K L Z k x hK hL hconn

/--
[not_conn_union_union_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma not_conn_union_union_cycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {K L Z : Finset I}
  {k zero : W}
-- given
  (hK : RootSpanning ends K k)
  (hL : RootSpanning ends L k)
  (hKZ : ¬ connK ends (K ∪ Z) k zero)
  (hLZ : ¬ connK ends (L ∪ Z) k zero) :
-- imply
  ¬ connK ends ((K ∪ L) ∪ Z) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.not_conn_union_union_cycle ends K L Z k zero hK hL hKZ hLZ

/--
[middleCycle_fourthCorner_gates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma middleCycle_fourthCorner_gates_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {M O X : Finset I}
  {j k l zero : W}
-- given
  (hloopM : ∀ i ∈ M, ¬ (ends i).IsDiag)
  (hloopO : ∀ i ∈ O, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hMsrc : sources ends M = {k, l})
  (hOsrc : sources ends O = {j, k})
  (hOsub : Subsingleton (boundarySector ends O ∅))
  (hMcard : Fintype.card (boundarySector ends M ∅) ≤ 2)
  (hXM : X ⊆ M)
  (hXsrc : sources ends X = ∅)
  (hXne : X ≠ ∅)
  (hOdisc : ¬ connK ends O k zero)
  (hMdisc : ¬ connK ends M k zero)
  (hOXdisc : ¬ connK ends (O ∪ X) k zero)
  (hMXdisc : ¬ connK ends (M \ X) k zero) :
-- imply
  ¬ connK ends (M ∪ O) k zero ∧ ¬ connK ends ((M \ X) ∪ O) k zero ∧ ¬ connK ends X k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.middleCycle_fourthCorner_gates ends M O X j k l zero hloopM hloopO hjk hkl hMsrc hOsrc hOsub hMcard hXM hXsrc hXne hOdisc hMdisc hOXdisc hMXdisc

/--
[outerCycle_fourthCorner_gates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma outerCycle_fourthCorner_gates_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {M O Y : Finset I}
  {j k l zero : W}
-- given
  (hloopM : ∀ i ∈ M, ¬ (ends i).IsDiag)
  (hloopO : ∀ i ∈ O, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hMsrc : sources ends M = {k, l})
  (hOsrc : sources ends O = {j, k})
  (hMsub : Subsingleton (boundarySector ends M ∅))
  (hOcard : Fintype.card (boundarySector ends O ∅) ≤ 2)
  (hYO : Y ⊆ O)
  (hYsrc : sources ends Y = ∅)
  (hYne : Y ≠ ∅)
  (hMdisc : ¬ connK ends M k zero)
  (hOdisc : ¬ connK ends O k zero)
  (hMYdisc : ¬ connK ends (M ∪ Y) k zero)
  (hOYdisc : ¬ connK ends (O \ Y) k zero) :
-- imply
  ¬ connK ends (M ∪ O) k zero ∧ ¬ connK ends (M ∪ (O \ Y)) k zero ∧ ¬ connK ends Y k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.outerCycle_fourthCorner_gates ends M O Y j k l zero hloopM hloopO hjk hkl hMsrc hOsrc hMsub hOcard hYO hYsrc hYne hMdisc hOdisc hMYdisc hOYdisc

/--
[colorClass_one_eq_middleMask_sdiff_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma colorClass_one_eq_middleMask_sdiff_two_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {c : ↑m → Fin 4} :
-- imply
  colorClass m c 1 = middleMask m c \ colorClass m c 2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_one_eq_middleMask_sdiff_two m c

/--
[rightRows_eq_cycleCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rightRows_eq_cycleCoordinates_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {q : ↑m → Fin 4} :
-- imply
  rowClass m q 0 = (middleMask m q \ colorClass m q 2) ∪ (outerMask m q \ colorClass m q 3) ∧ rowClass m q 1 = colorClass m q 2 ∪ colorClass m q 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightRows_eq_cycleCoordinates m q

/--
[rightRows_eq_of_cycleCoordinates_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rightRows_eq_of_cycleCoordinates_empty_eq
  [Fintype I]
  [DecidableEq I]
  {m M O : Finset I}
  {q : ↑m → Fin 4}
-- given
  (hM : middleMask m q = M)
  (hO : outerMask m q = O)
  (h2 : colorClass m q 2 = ∅)
  (h3 : colorClass m q 3 = ∅) :
-- imply
  rowClass m q 0 = M ∪ O ∧ rowClass m q 1 = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightRows_eq_of_cycleCoordinates_empty m M O q hM hO h2 h3

/--
[rightRows_eq_of_middleCycleCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rightRows_eq_of_middleCycleCoordinate_eq
  [Fintype I]
  [DecidableEq I]
  {m M O X : Finset I}
  {q : ↑m → Fin 4}
-- given
  (hM : middleMask m q = M)
  (hO : outerMask m q = O)
  (h2 : colorClass m q 2 = X)
  (h3 : colorClass m q 3 = ∅) :
-- imply
  rowClass m q 0 = (M \ X) ∪ O ∧ rowClass m q 1 = X := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightRows_eq_of_middleCycleCoordinate m M O X q hM hO h2 h3

/--
[rightRows_eq_of_outerCycleCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rightRows_eq_of_outerCycleCoordinate_eq
  [Fintype I]
  [DecidableEq I]
  {m M O Y : Finset I}
  {q : ↑m → Fin 4}
-- given
  (hM : middleMask m q = M)
  (hO : outerMask m q = O)
  (h2 : colorClass m q 2 = ∅)
  (h3 : colorClass m q 3 = Y) :
-- imply
  rowClass m q 0 = M ∪ (O \ Y) ∧ rowClass m q 1 = Y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightRows_eq_of_outerCycleCoordinate m M O Y q hM hO h2 h3

/--
[not_conn_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma not_conn_empty_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {k zero : W}
-- given
  (hk0 : k ≠ zero) :
-- imply
  ¬ connK ends ∅ k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.not_conn_empty ends hk0

/--
[rightMaskCycleTranslate_disconnects_of_first_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_disconnects_of_first_empty_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : c ≠ d)
  (hcEmpty : leftMaskCyclePair ends m j k l zero p c = emptyMaskCyclePair ends p)
  (hcycle : Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  RowsDisconnect ends m (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_disconnects_of_first_empty ends m j k l zero hloop hjk hkl hk0 p c d hcd hcEmpty hcycle q

/--
[rightMaskCycleTranslate_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_comm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {c d q : ↑m → Fin 4} :
-- imply
  rightMaskCycleTranslate m c d q = rightMaskCycleTranslate m d c q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_comm m c d q

/--
[rightMaskCycleTranslate_disconnects_of_cycleProduct_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rightMaskCycleTranslate_disconnects_of_cycleProduct_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : c ≠ d)
  (hcycle : Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  RowsDisconnect ends m (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskCycleTranslate_disconnects_of_cycleProduct_le_two ends m j k l zero hloop hjk hkl hk0 p c d hcd hcycle q

/--
[exists_rightMaskFiber_pair_of_cycleProduct_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma exists_rightMaskFiber_pair_of_cycleProduct_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : c ≠ d)
  (hcycle : Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  ∃ q r : rightMaskFiber ends m j k l zero p, q ≠ r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_rightMaskFiber_pair_of_cycleProduct_le_two ends m j k l zero hloop hjk hkl hk0 p c d hcd hcycle

/--
[rowDataRepairHall_of_cycleProduct_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean)
-/
@[path]
private lemma rowDataRepairHall_of_cycleProduct_le_two_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcycle : ∀ p : Finset I × Finset I, Fintype.card (boundarySector ends p.1 ∅) * Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_cycleProduct_le_two ends m j k l zero hloop hjk hkl hk0 hcycle


-- created on 2026-10-23
