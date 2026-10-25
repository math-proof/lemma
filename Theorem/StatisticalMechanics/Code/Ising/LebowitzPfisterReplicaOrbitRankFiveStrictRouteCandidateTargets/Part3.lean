/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.Part2


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot_folded
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    let route :=
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
        G sites hsite q hcard z d
    lpReplicaOrbitFoldedSlotEnds G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
          G sites hsite q z d) =
      s(Sum.inl (sites route.u), Sum.inl (sites route.v)) := by
  dsimp only
  let a := z.toAggregate G sites q
  let route :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d
  unfold
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
  rw [lpReplicaOrbitFoldedSlotEnds_copy]
  rw [← route.hfold]
  congr 2
  exact
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d
      G sites hsite q hcard z d).symm


end
end StatMech.Ising
