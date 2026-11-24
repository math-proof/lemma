module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.Part4
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.Part3
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

instance lpReplicaRankFiveStrictRouteCandidateTargetsDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


end
end StatMech.Ising
