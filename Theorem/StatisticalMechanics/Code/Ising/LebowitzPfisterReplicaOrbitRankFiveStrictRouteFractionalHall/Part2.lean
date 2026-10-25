/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.FractionalHall
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part3


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (degree : Nat) (y : LPReplicaAggregateDecoratedTarget G sites q)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    z ∈ LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard degree y ↔
      LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y ∧
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z).card = degree := by
  classical
  simp [LPReplicaAggregateRankFiveStrictRouteIncomingDegree]


end
end StatMech.Ising
