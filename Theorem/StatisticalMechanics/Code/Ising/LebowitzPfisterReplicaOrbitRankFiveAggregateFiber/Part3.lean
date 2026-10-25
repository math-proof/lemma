/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
      G sites i j q u).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  have hz' := Finset.mem_filter.mp hz
  have hw' := Finset.mem_filter.mp hw
  apply lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
    G sites i j q u hz'.1 hw'.1
  exact (lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
    G sites hsite hij q hcard z hz'.2).trans
      (lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
        G sites hsite hij q hcard w hw'.2).symm


end
end StatMech.Ising
