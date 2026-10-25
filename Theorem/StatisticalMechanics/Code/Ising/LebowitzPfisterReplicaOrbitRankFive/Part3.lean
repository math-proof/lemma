/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFour
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitMultiplicityClass
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
        G sites i j q u ↔
      z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u ∧
        LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive
          G sites i j q z := by
  classical
  simp [lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive]


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
      G sites i j q u).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  rw [mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive]
    at hz hw
  apply lpReplicaOffdiagDecoratedSource_rank_five_saturated_eq_of_crossTrace_eq
    G sites hsite hij q hcard z w hz.2 hw.2
  exact (Finset.mem_filter.mp hz.1).2.trans
    (Finset.mem_filter.mp hw.1).2.symm

end
end StatMech.Ising
