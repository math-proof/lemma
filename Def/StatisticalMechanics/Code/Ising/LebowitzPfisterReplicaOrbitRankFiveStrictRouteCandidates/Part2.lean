/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.Part2


namespace StatMech.Ising

noncomputable section

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    Finset (Copy (lpReplicaCurrentGraph G sites)
      (z.toAggregate G sites q).2.2.2.1.1.1) := by
  classical
  let a := z.toAggregate G sites q
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  exact Finset.univ.filter fun d =>
    d ∈ Finset.univ \ {c} ∧
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
        endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
        endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
      ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag

end
end StatMech.Ising
