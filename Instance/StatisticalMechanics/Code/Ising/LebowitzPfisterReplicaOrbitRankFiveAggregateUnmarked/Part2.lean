module
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.Part3
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part3
open Finset
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable instance
    instFintypeLPReplicaAggregateUnmarkedSaturatedSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
  unfold LPReplicaAggregateUnmarkedSaturatedSourceRankFive
  infer_instance


end
end StatMech.Ising
