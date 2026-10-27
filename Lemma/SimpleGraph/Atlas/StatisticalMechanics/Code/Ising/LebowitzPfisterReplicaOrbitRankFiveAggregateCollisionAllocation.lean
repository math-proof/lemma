import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.Part3
open Finset StatMech StatMech.Ising


/--
[lpReplicaLowRow_parallelInactive_exists_maskFourTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma lpReplicaLowRow_parallelInactive_exists_maskFourTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {k c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z)
  (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hk : k.1.1 = lpReplicaCurrentSeamEdge sites i ∨ k.1.1 = lpReplicaCurrentSeamEdge sites j)
  (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hck : c.1.1 = k.1.1)
  (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (false, false)) :
-- imply
  ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) 4 ∧ lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∪ {lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1 z.1.1.2 z.2.2 c} := by
-- proof
  apply StatMech.Ising.lpReplicaLowRow_parallelInactive_exists_maskFourTarget G sites hsite hij q hcard z hlow k c hkK hk hcC hck hctag

/--
[lpReplicaLowRowCollisionParallelData_inactiveSlotPair_eq_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma lpReplicaLowRowCollisionParallelData_inactiveSlotPair_eq_complement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowCollisionParallelData G sites i j q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z) :
-- imply
  ({lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1 z.1.1.2 z.2.2 d.inactiveCopy₀, lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1 z.1.1.2 z.2.2 d.inactiveCopy₁} : Finset (LPReplicaOrbitCommonSlot G sites q)) = Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowCollisionParallelData_inactiveSlotPair_eq_complement G sites hsite hij q hcard z hlow d

/--
[finset_union_singleton_eq_sdiff_of_pair_eq_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma finset_union_singleton_eq_sdiff_of_pair_eq_complement_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype A]
  [DecidableEq A]
  {M : Finset A}
  {a b : A}
-- given
  (hab : a ≠ b)
  (hpair : ({a, b} : Finset A) = Finset.univ \ M) :
-- imply
  M ∪ {b} = Finset.univ \ {a} := by
-- proof
  apply StatMech.Ising.finset_union_singleton_eq_sdiff_of_pair_eq_complement M hab hpair

/--
[lpReplicaLowRowCrossTraceOutput_collision_maskFour_card_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma lpReplicaLowRowCrossTraceOutput_collision_maskFour_card_ge_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
  {z w : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive G sites i j q u)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hzw : z ≠ w)
  (hout : lpReplicaLowRowCrossTraceOutput G sites hsite hij q hcard u z = lpReplicaLowRowCrossTraceOutput G sites hsite hij q hcard u w) :
-- imply
  3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive G sites i j q u 4).card := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowCrossTraceOutput_collision_maskFour_card_ge_three G sites hsite hij q hcard u z w hzw hout

/--
[lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_eq
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
  (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive G sites i j q u).card ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target G sites hsite hij q hcard u

/--
[lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_eq_sum_traceFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_eq_sum_traceFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q).card = ∑ u : LPReplicaOrbitFourColorSlotState G sites q, (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_eq_sum_traceFibers G sites i j q

/--
[lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_le_target_eq
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
  (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q).card ≤ Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_le_target G sites hsite hij q hcard

/--
[card_lpReplicaAggregateLowOrResolvableHighSourceRankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) = ∑ i : I, ∑ j : I, if i = j then 0 else (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q).card := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateLowOrResolvableHighSourceRankFive G sites q

/--
[card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean)
-/
@[path]
private lemma card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Fintype.card (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target G sites hsite q hcard


-- created on 2026-10-23
