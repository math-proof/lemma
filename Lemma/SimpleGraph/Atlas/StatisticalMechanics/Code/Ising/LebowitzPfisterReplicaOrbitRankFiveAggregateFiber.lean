import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.Part4
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots_eq
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
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) = lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots G sites hsite hij q hcard z hlow

/--
[lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card_eq
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
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z) :
-- imply
  (lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)).card = 3 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card G sites hsite hij q hcard z hlow

/--
[lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {e : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z)
  (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) :
-- imply
  lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1 z.1.1.2 z.2.2 e) = e.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_of_inactive G sites hsite hij q hcard z hlow e heC

/--
[lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_injOn_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_injOn_active_eq
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
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z) :
-- imply
  Set.InjOn (lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)) (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_lowRow_crossTrace_edge_injOn_active G sites hsite hij q hcard z hlow

/--
[lpReplicaOffdiagDecoratedSource_rank_five_lowRow_inactivePair_mem_eligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_lowRow_inactivePair_mem_eligible_eq
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
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z) :
-- imply
  Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∈ lpReplicaEligibleInactivePairs (lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_lowRow_inactivePair_mem_eligible G sites hsite hij q hcard z hlow

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three_eq
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
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive G sites i j q u).card ≤ 3 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three G sites hsite hij q hcard u

/--
[lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ_eq
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
  (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive G sites i j q z) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) = Finset.univ := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ G sites hsite hij q hcard z hhigh

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one_eq
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
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive G sites i j q u).card ≤ 1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one G sites hsite hij q hcard u

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high_eq
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
  lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u = lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive G sites i j q u := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high G sites hsite hij q hcard u

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four_eq
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
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card ≤ 4 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four G sites hsite hij q hcard u


-- created on 2026-10-23
