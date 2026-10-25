/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagRankFiveOutputCollisionClass_card_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    (lpReplicaOffdiagRankFiveOutputCollisionClass
      G sites i j q output y).card ≤ 4 := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four
      G sites hsite hij q hcard
        (lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y))


end
end StatMech.Ising
