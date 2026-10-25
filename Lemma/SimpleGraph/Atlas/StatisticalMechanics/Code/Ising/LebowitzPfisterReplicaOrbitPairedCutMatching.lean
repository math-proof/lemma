import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part4
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagCoupledPairedMatch_iff_output](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedMatch_iff_output_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagCoupledPairedMatch G sites i j q z y ↔ LPReplicaOffdiagCoupledPairedOutput G sites i j q y := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedMatch_iff_output G sites i j q z y

/--
[lpReplicaOffdiagCoupledPairedSource_card_eq_sum_profileFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedSource_card_eq_sum_profileFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) = ∑ m ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q, (lpReplicaOffdiagDecoratedSourcesAtProfile G sites i j q m).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedSource_card_eq_sum_profileFibers G sites i j q

/--
[lpReplicaOffdiagCoupledPairedOutputs_card_eq_sum_profileFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedOutputs_card_eq_sum_profileFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card = ∑ m ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q, (lpReplicaOffdiagCoupledPairedOutputsAtProfile G sites i j q m).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedOutputs_card_eq_sum_profileFibers G sites i j q

/--
[lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {a : LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation G sites i j q a

/--
[lpReplicaOffdiagCoupledPairedHall_of_outputCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedHall_of_outputCard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
-- imply
  LPReplicaOffdiagCoupledPairedHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedHall_of_outputCard G sites i j q hcard

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard G sites i j q hcard

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedProfileAllocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedProfileAllocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {a : LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedProfileAllocation G sites i j q a

/--
[lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hcard : ∀ q i j, i ≠ j -> Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards G sites beta J hf r hbeta hJ hhf hr hcard

/--
[lpReplicaAggregateProfileOrbitInequality_of_coupledPairedProfileAllocations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_coupledPairedProfileAllocations_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (halloc : ∀ q i j, i ≠ j -> LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_coupledPairedProfileAllocations G sites beta J hf r hbeta hJ hhf hr halloc

/--
[lpReplicaMatchingDisconn_le_of_coupledPairedOutputCards](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconn_le_of_coupledPairedOutputCards_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hcard : ∀ q i j, i ≠ j -> Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnTwo H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= 2 * lpMatchingDisconnZero H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnOne H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconn_le_of_coupledPairedOutputCards G sites beta J hf r hbeta hJ hhf hr hcard

/--
[lpReplicaMatchingDisconn_le_of_coupledPairedProfileAllocations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconn_le_of_coupledPairedProfileAllocations_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (halloc : ∀ q i j, i ≠ j -> LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnTwo H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= 2 * lpMatchingDisconnZero H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnOne H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconn_le_of_coupledPairedProfileAllocations G sites beta J hf r hbeta hJ hhf hr halloc

/--
[lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_coupledPairedProfileAllocations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean)
-/
@[path]
private lemma lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_coupledPairedProfileAllocations_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (halloc : ∀ q i j, i ≠ j -> LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r (∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_coupledPairedProfileAllocations G sites beta J hf r hbeta hJ hhf hr halloc


-- created on 2026-10-23
