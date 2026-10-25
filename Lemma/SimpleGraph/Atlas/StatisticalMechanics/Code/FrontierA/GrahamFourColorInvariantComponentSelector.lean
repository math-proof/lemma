import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantComponentSelector
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[invariantMiddleTransfer_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean)
-/
@[path]
private lemma invariantMiddleTransfer_subset_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  invariantMiddleTransfer ends m c k ⊆ middleMask m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.invariantMiddleTransfer_subset ends m c k

/--
[invariantOuterTransfer_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean)
-/
@[path]
private lemma invariantOuterTransfer_subset_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j zero : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  invariantOuterTransfer ends m c j zero ⊆ outerMask m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.invariantOuterTransfer_subset ends m c j zero

/--
[invariantMiddleTransfer_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean)
-/
@[path]
private lemma invariantMiddleTransfer_sources_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  sources ends (invariantMiddleTransfer ends m c k) = {k, l} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.invariantMiddleTransfer_sources hloop hjk hkl hc

/--
[invariantOuterTransfer_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean)
-/
@[path]
private lemma invariantOuterTransfer_sources_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  sources ends (invariantOuterTransfer ends m c j zero) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.invariantOuterTransfer_sources hloop hjk hkl hc

/--
[invariantMiddleTransfer_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean)
-/
@[path]
private lemma invariantMiddleTransfer_balancedSwap_eq
  [Fintype I]
  [DecidableEq I]
  {m X Y : Finset I}
  {k : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  invariantMiddleTransfer ends m (balancedSwap m X Y c) k = invariantMiddleTransfer ends m c k := by
-- proof
  apply StatMech.GrahamGHS.FourColor.invariantMiddleTransfer_balancedSwap ends m X Y c k

/--
[invariantOuterTransfer_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean)
-/
@[path]
private lemma invariantOuterTransfer_balancedSwap_eq
  [Fintype I]
  [DecidableEq I]
  {m X Y : Finset I}
  {j zero : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  invariantOuterTransfer ends m (balancedSwap m X Y c) j zero = invariantOuterTransfer ends m c j zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.invariantOuterTransfer_balancedSwap ends m X Y c j zero

/--
[invariantComponentSelector_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean)
-/
@[path]
private lemma invariantComponentSelector_balancedSwap_eq
  [Fintype I]
  [DecidableEq I]
  {m X Y : Finset I}
  {j k zero : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  invariantComponentSelector ends m j k zero (balancedSwap m X Y c) = invariantComponentSelector ends m j k zero c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.invariantComponentSelector_balancedSwap ends m X Y j k zero c

/--
[GrahamFiberMinor_of_invariantComponent_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_invariantComponent_disconnects_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hdisc : ∀ c : ↑m -> Fin 4, LeftPattern ends m {j, k} {k, l} k zero c -> RowsDisconnect ends m (balancedSwap m (invariantMiddleTransfer ends m c k) (invariantOuterTransfer ends m c j zero) c) k zero) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_invariantComponent_disconnects ends m j k l zero hloop hjk hkl hdisc


-- created on 2026-10-23
