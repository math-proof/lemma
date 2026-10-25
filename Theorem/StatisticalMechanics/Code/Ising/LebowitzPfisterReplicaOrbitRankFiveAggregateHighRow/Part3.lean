/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
      G sites i j q u).card <= 1 := by
  classical
  calc
    (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
        G sites i j q u).card <=
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
        G sites i j q u).card := by
      apply Finset.card_le_card
      intro z hz
      simp only [lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive,
        lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive,
        Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.1⟩
    _ <= 1 :=
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one
        G sites hsite hij q hcard u


theorem lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
      G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  classical
  have hsource :=
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one
      G sites hsite hij q hcard u
  by_cases hempty :
      (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
        G sites i j q u).Nonempty
  · obtain ⟨z, hz⟩ := hempty
    have hz' := Finset.mem_filter.mp hz
    have htarget :=
      lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_resolvableHighRow
        G sites hsite hij q hcard z hz'.2
    have htrace := (Finset.mem_filter.mp hz'.1).2
    rw [htrace] at htarget
    exact Nat.le_trans hsource (Finset.card_pos.mpr htarget)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty]
    exact Nat.zero_le _


end
end StatMech.Ising
