/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.FractionalHall
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def LPReplicaAggregateRankFiveStrictRouteIncomingDegree
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (degree : Nat) (y : LPReplicaAggregateDecoratedTarget G sites q) :
    Finset (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
  classical
  exact Finset.univ.filter fun z =>
    LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y ∧
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card = degree

end
end StatMech.Ising
