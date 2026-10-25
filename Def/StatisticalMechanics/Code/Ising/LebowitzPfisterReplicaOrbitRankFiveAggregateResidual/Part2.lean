/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregateRankFiveHandledTargetImage
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.image
    (lpReplicaAggregateLowOrResolvableHighRankFiveEmbedding
      G sites hsite q hcard)


noncomputable def LPReplicaAggregateRankFiveSelectedResidualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) : Prop := by
  classical
  exact forall k : I,
    Fintype.card
        {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q //
          lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
            (z.toAggregate G sites q) = k} <=
      Fintype.card
        {y : {y : LPReplicaAggregateDecoratedTarget G sites q //
          y ∉ lpReplicaAggregateRankFiveHandledTargetImage
            G sites hsite q hcard} // y.1.2.1 = k}


end
end StatMech.Ising
