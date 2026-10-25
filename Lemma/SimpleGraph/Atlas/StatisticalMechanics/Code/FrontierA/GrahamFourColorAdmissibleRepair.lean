import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[mem_balancedRepairs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma mem_balancedRepairs_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {k zero : W}
  {Y : Finset ι}
-- given
  (ends : ι -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  Y ∈ balancedRepairs ends m X k zero c ↔ BalancedRepairAdmissible ends m X k zero c Y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_balancedRepairs_iff ends m X k zero c Y

/--
[balancedRepairAdmissible_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma balancedRepairAdmissible_swap_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {k zero : W}
  {Y : Finset ι}
-- given
  (ends : ι -> Sym2 W)
  (c : ↑m -> Fin 4)
  (hY : BalancedRepairAdmissible ends m X k zero c Y) :
-- imply
  BalancedRepairAdmissible ends m X k zero (balancedSwap m X Y c) Y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.balancedRepairAdmissible_swap ends m X k zero c Y hY

/--
[balancedRepairAdmissible_swap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma balancedRepairAdmissible_swap_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {k zero : W}
  {Y : Finset ι}
-- given
  (ends : ι -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  BalancedRepairAdmissible ends m X k zero (balancedSwap m X Y c) Y ↔ BalancedRepairAdmissible ends m X k zero c Y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.balancedRepairAdmissible_swap_iff ends m X k zero c Y

/--
[mem_balancedRepairs_swap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma mem_balancedRepairs_swap_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {k zero : W}
  {Y : Finset ι}
-- given
  (ends : ι -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  Y ∈ balancedRepairs ends m X k zero (balancedSwap m X Y c) ↔ Y ∈ balancedRepairs ends m X k zero c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_balancedRepairs_swap_iff ends m X k zero c Y

/--
[balancedRepairRelated_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma balancedRepairRelated_symm_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {k zero : W}
  {c d : ↑m -> Fin 4}
-- given
  (ends : ι -> Sym2 W)
  (h : BalancedRepairRelated ends m X k zero c d) :
-- imply
  BalancedRepairRelated ends m X k zero d c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.balancedRepairRelated_symm ends m X k zero h

/--
[subtype_mem_colorClass_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma subtype_mem_colorClass_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {i : ↑m}
  {a : Fin 4}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  (i : ι) ∈ colorClass m c a ↔ c i = a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.subtype_mem_colorClass_iff m c i a

/--
[balancedSwap_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma balancedSwap_difference_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
-- given
  (c d : ↑m -> Fin 4)
  (hmid : middleMask m c = middleMask m d)
  (hout : outerMask m c = outerMask m d) :
-- imply
  balancedSwap m (balancedMiddleDifference m c d) (balancedOuterDifference m c d) c = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.balancedSwap_difference m c d hmid hout

/--
[balancedMiddleDifference_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma balancedMiddleDifference_subset_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
-- given
  (c d : ↑m -> Fin 4)
  (hmid : middleMask m c = middleMask m d) :
-- imply
  balancedMiddleDifference m c d ⊆ middleMask m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.balancedMiddleDifference_subset m c d hmid

/--
[balancedOuterDifference_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma balancedOuterDifference_subset_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
-- given
  (c d : ↑m -> Fin 4)
  (hout : outerMask m c = outerMask m d) :
-- imply
  balancedOuterDifference m c d ⊆ outerMask m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.balancedOuterDifference_subset m c d hout

/--
[left_right_sameMasks_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma left_right_sameMasks_admissible_eq
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι -> Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c d : ↑m -> Fin 4}
-- given
  (hc : LeftPattern ends m {j, k} {k, l} k zero c)
  (hd : RightPattern ends m {j, k} {k, l} k zero d)
  (hmid : middleMask m c = middleMask m d)
  (hout : outerMask m c = outerMask m d) :
-- imply
  let X := balancedMiddleDifference m c d let Y := balancedOuterDifference m c d X ⊆ middleMask m c ∧ Y ⊆ outerMask m c ∧ sources ends X = {k, l} ∧ sources ends Y = ∅ ∧ BalancedRepairAdmissible ends m X k zero c Y ∧ balancedSwap m X Y c = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.left_right_sameMasks_admissible hc hd hmid hout

/--
[leftFiber_card_eq_sum_maskFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma leftFiber_card_eq_sum_maskFibers_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {j k l zero : W}
-- given
  (ends : ι -> Sym2 W) :
-- imply
  Fintype.card (leftFiber ends m {j, k} {k, l} k zero) = ∑ p : Finset ι × Finset ι, Fintype.card (leftMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftFiber_card_eq_sum_maskFibers ends m j k l zero

/--
[rightFiber_card_eq_sum_maskFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma rightFiber_card_eq_sum_maskFibers_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {j k l zero : W}
-- given
  (ends : ι -> Sym2 W) :
-- imply
  Fintype.card (rightFiber ends m {j, k} {k, l} k zero) = ∑ p : Finset ι × Finset ι, Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightFiber_card_eq_sum_maskFibers ends m j k l zero

/--
[GrahamFiberMinor_of_maskwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_maskwise_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {j k l zero : W}
-- given
  (ends : ι -> Sym2 W)
  (hmask : ∀ p : Finset ι × Finset ι, Fintype.card (leftMaskFiber ends m j k l zero p) <= Fintype.card (rightMaskFiber ends m j k l zero p)) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_maskwise ends m j k l zero hmask

/--
[rightMaskFiber_nonempty_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean)
-/
@[path]
private lemma rightMaskFiber_nonempty_of_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι -> Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {p : Finset ι × Finset ι}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  Nonempty (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c


-- created on 2026-10-23
