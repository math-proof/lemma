/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTarget
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget_selectedSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget
      G sites hsite q hcard z).2.1 =
      lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
        (z.toAggregate G sites q) := by
  classical
  unfold lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteTarget
  dsimp only

end
end StatMech.Ising
