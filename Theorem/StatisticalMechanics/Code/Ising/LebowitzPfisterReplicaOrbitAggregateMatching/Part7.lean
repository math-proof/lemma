/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaAggregateSelectedTargetFiber
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) (k : I) :
    Fintype.card
        {y : LPReplicaAggregateDecoratedTarget G sites q // y.2.1 = k} =
      ∑ j : I, 2 * Fintype.card
        (LPReplicaDecoratedOrbitAtom G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q) := by
  rw [Fintype.card_congr
    (lpReplicaAggregateSelectedTargetFiberEquiv G sites q k),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma,
    Finset.mul_sum]


theorem lpReplicaAggregateSelectedSeamCapacity_iff_explicit
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaAggregateSelectedSeamCapacity G sites hsite q <->
      forall k : I,
        Fintype.card {z : LPReplicaAggregateDecoratedSource G sites q //
            lpReplicaAggregateDecoratedSourceSelectedSeam
              G sites hsite q z = k} <=
          ∑ j : I, 2 * Fintype.card
            (LPReplicaDecoratedOrbitAtom G sites
              (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites)
                (lpReplicaCurrentRight sites) k)
              (lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites)
                  (lpReplicaCurrentRight sites) j ∆
                lpMatchingGhostSource
                  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                  lpReplicaCurrentGhost1) q) := by
  unfold LPReplicaAggregateSelectedSeamCapacity
  simp_rw [card_lpReplicaAggregateSelectedTargetFiber]

end
end StatMech.Ising
