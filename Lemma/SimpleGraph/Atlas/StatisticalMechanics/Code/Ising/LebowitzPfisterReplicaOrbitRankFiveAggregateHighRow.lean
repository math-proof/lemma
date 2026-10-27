import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsat : lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false = Finset.univ)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites j) :
-- imply
  ∃ y : LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inr y)).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam G sites q z hsat c hc

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_resolvableHighRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_resolvableHighRow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hresolve : LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive G sites i j q z) :
-- imply
  (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_resolvableHighRow G sites hsite hij q hcard z hresolve

/--
[lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive G sites i j q u).card <= 1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one G sites hsite hij q hcard u

/--
[lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive G sites i j q u).card <= (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_target G sites hsite hij q hcard u

/--
[lpReplicaOffdiagDecoratedTargetToAggregate_crossTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedTargetToAggregate_crossTrace_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedTargetCrossTrace G sites q (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y) = lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedTargetToAggregate_crossTrace G sites i j q y

/--
[lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_eq_sum_traceFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_eq_sum_traceFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagResolvableHighRowSourcesRankFive G sites i j q).card = ∑ u : LPReplicaOrbitFourColorSlotState G sites q, (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_eq_sum_traceFibers G sites i j q

/--
[lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_le_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaOffdiagResolvableHighRowSourcesRankFive G sites i j q).card <= Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_le_target G sites hsite hij q hcard

/--
[card_lpReplicaAggregateResolvableHighRowSourceRankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma card_lpReplicaAggregateResolvableHighRowSourceRankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaAggregateResolvableHighRowSourceRankFive G sites q) = ∑ i : I, ∑ j : I, if i = j then 0 else (lpReplicaOffdiagResolvableHighRowSourcesRankFive G sites i j q).card := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateResolvableHighRowSourceRankFive G sites q

/--
[sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean)
-/
@[path]
private lemma sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (∑ i : I, ∑ j : I, Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q)) = Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
-- proof
  apply StatMech.Ising.sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate G sites q


-- created on 2026-10-23
