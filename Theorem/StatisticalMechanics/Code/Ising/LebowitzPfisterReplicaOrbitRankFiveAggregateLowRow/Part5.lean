/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaLowRowCrossTraceOutput_collision_card_ge_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z w : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u)) (hzw : z ≠ w)
    (hout : lpReplicaLowRowCrossTraceOutput
      G sites hsite hij q hcard u z =
        lpReplicaLowRowCrossTraceOutput
          G sites hsite hij q hcard u w) :
    3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber
      G sites i j q u).card := by
  classical
  let d := lpReplicaLowRowCrossTraceOutput_collision_parallelData
    G sites hsite hij q hcard u z w hzw hout
  have hzmem := Finset.mem_filter.mp z.2
  rcases d.markedSeam with hi | hj
  · have hthree :=
      lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_iSeam_parallelPair
        G sites hsite hij q hcard z.1 hzmem.2.1 d.activeCopy
        d.inactiveCopy₀ d.inactiveCopy₁ d.active_mem hi d.inactive₀_mem
        d.inactive₁_mem d.inactive₀_parallel d.inactive₁_parallel
        d.inactive₀_tag d.inactive₁_tag d.inactive_ne
    have htrace := (Finset.mem_filter.mp hzmem.1).2
    simpa only [htrace] using hthree
  · have hthree :=
      lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_jSeam_parallelPair
        G sites hsite hij q hcard z.1 hzmem.2.1 d.activeCopy
        d.inactiveCopy₀ d.inactiveCopy₁ d.active_mem hj d.inactive₀_mem
        d.inactive₁_mem d.inactive₀_parallel d.inactive₁_parallel
        d.inactive₀_tag d.inactive₁_tag d.inactive_ne
    have htrace := (Finset.mem_filter.mp hzmem.1).2
    simpa only [htrace] using hthree


theorem lpReplicaOffdiagLowRowCrossTraceFiberRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u).card ≤
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  classical
  let f := lpReplicaLowRowCrossTraceOutput
    G sites hsite hij q hcard u
  by_cases hf : Function.Injective f
  · simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective f hf
  · obtain ⟨z, w, houtput, hzw⟩ := Function.not_injective_iff.mp hf
    exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
      G sites hsite hij q hcard u).trans
        (lpReplicaLowRowCrossTraceOutput_collision_card_ge_three
          G sites hsite hij q hcard u z w hzw houtput)


end
end StatMech.Ising
