/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregateResolvableHighRowRankFiveEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateResolvableHighRowSourceRankFive G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  rw [card_lpReplicaAggregateResolvableHighRowSourceRankFive,
    ← sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij]
    exact lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_le_target
      G sites hsite hij q hcard

end
end StatMech.Ising
