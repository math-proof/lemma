/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z).1.1 =
      lpReplicaCurrentSeamEdge sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
          (z.toAggregate G sites q)) :=
  Classical.choose_spec
    (lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
      G sites hsite q (z.toAggregate G sites q))


end
end StatMech.Ising
