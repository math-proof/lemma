/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.Part2


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregateRankFiveEmbedding_of_residualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (hresidual : LPReplicaAggregateRankFiveResidualCapacity G sites q) :
    LPReplicaAggregateDecoratedSource G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  exact
    (lpReplicaAggregateRankFiveResidualCapacity_iff_card_le_target
      G sites hsite q hcard).mp hresidual


noncomputable def lpReplicaAggregateRankFiveEmbedding_of_selectedResidualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (hselected : LPReplicaAggregateRankFiveSelectedResidualCapacity
      G sites hsite q hcard) :
    LPReplicaAggregateDecoratedSource G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q :=
  lpReplicaAggregateRankFiveEmbedding_of_residualCapacity
    G sites hsite q hcard
      (lpReplicaAggregateRankFiveResidualCapacity_of_selected
        G sites hsite q hcard hselected)


end
end StatMech.Ising
