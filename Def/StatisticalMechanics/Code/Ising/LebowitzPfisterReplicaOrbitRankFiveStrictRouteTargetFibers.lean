/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (d : LPReplicaOrbitCommonSlot G sites q) : Prop :=
  let state := lpReplicaAggregateDecoratedTargetSlotState G sites q y
  let row := lpReplicaOrbitFourColorSlotRowMask G sites q state
  let ends := lpReplicaOrbitFourColorSlotEnds G sites q state
  ¬ (lpReplicaOrbitFoldedSlotEnds G sites q d).IsDiag ∧
    d ∈ row ∧
      ∀ x ∈ ends d, ∃ e ∈ row, e ≠ d ∧ x ∈ ends e


end
end StatMech.Ising
