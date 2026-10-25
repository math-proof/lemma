/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem
    lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_eq_sum_traceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
      G sites i j q).card =
      ∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
          G sites i j q u).card := by
  classical
  let trace := lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q
  simpa only [lpReplicaOffdiagLowOrResolvableHighSourcesRankFive,
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive,
    lpReplicaOffdiagLowRowSourcesRankFive,
    lpReplicaOffdiagResolvableHighRowSourcesRankFive,
    lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive,
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive,
    lpReplicaOffdiagDecoratedSourceCrossTraceFiber, trace,
    Finset.filter_union, Finset.filter_filter,
    and_comm, and_left_comm, and_assoc] using
      Finset.card_eq_sum_card_fiberwise
        (s := lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
          G sites i j q)
        (t := (Finset.univ : Finset
          (LPReplicaOrbitFourColorSlotState G sites q)))
        (f := trace) (fun _ _ => Finset.mem_univ _)


theorem lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
      G sites i j q).card ≤
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  rw [lpReplicaOffdiagLowOrResolvableHighSourcesRankFive_card_eq_sum_traceFibers]
  calc
    (∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
          G sites i j q u).card) ≤
      ∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card := by
      exact Finset.sum_le_sum fun u _ =>
        lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target
          G sites hsite hij q hcard u
    _ = (lpReplicaOffdiagBalancedOutputs G sites i j q).card := by
      symm
      simpa using
        (lpReplicaOffdiagBalancedOutputs_card_eq_sum_crossTraceFibers
          G sites i j q
          (Finset.univ : Finset
            (LPReplicaOrbitFourColorSlotState G sites q))
          (fun _ _ => Finset.mem_univ _))
    _ ≤ Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)


end
end StatMech.Ising
