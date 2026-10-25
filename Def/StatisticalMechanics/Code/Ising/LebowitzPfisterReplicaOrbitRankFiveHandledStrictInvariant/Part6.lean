/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part6


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def
    lpReplicaAggregateRankFiveStrictRouteComponentAllocation_of_targetLoad_lt_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y t : LPReplicaAggregateDecoratedTarget G sites q)
    (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y)
    (hslack :
      (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z t) < 1) :
    Unit ⊕ ↑(LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
        G sites hsite q hcard y) ↪
      ↑(LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y) := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_coe] using
    lpReplicaAggregateRankFiveStrictRoute_one_add_componentSources_card_le_of_targetLoad_lt_one
      G sites hsite q hcard y t ht hslack

end
end StatMech.Ising
