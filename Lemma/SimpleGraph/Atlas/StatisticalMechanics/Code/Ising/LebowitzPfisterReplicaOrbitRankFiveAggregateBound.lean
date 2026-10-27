import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound
open Finset StatMech StatMech.Ising


/--
[lpReplicaAggregateRankFiveSourceKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateBound.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveSourceKey_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Function.Injective (lpReplicaAggregateRankFiveSourceKey G sites hsite q hcard u) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveSourceKey_injective G sites hsite q hcard u

/--
[card_lpReplicaAggregateSourceCrossTraceFiber_rank_five_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateBound.lean)
-/
@[path]
private lemma card_lpReplicaAggregateSourceCrossTraceFiber_rank_five_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Fintype.card (LPReplicaAggregateSourceCrossTraceFiber G sites q u) <= Fintype.card I * (Fintype.card I * 4) := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateSourceCrossTraceFiber_rank_five_le G sites hsite q hcard u


-- created on 2026-10-23
