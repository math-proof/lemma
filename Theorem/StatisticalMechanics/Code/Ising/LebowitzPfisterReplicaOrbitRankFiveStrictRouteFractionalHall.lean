/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.FractionalHall
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part2


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaAggregateRankFiveStrictRouteWeight_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    0 ≤ LPReplicaAggregateRankFiveStrictRouteWeight
      G sites hsite q hcard z y := by
  classical
  unfold LPReplicaAggregateRankFiveStrictRouteWeight
  split
  · positivity
  · exact le_rfl

theorem LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hnot : ¬ LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y) :
    LPReplicaAggregateRankFiveStrictRouteWeight
      G sites hsite q hcard z y = 0 := by
  classical
  simp [LPReplicaAggregateRankFiveStrictRouteWeight, hnot]


end
end StatMech.Ising
