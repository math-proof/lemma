/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaOffdiagCoupledPairedProfileAllocation
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  flow : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ->
    ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Nat
  covers : ∀ m ∈
      lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
    (lpReplicaOffdiagDecoratedSourcesAtProfile G sites i j q m).card <=
      ∑ n ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
        flow m n
  capacity : ∀ n ∈
      lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
    (∑ m ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
        flow m n) <=
      (lpReplicaOffdiagCoupledPairedOutputsAtProfile
        G sites i j q n).card


end
end StatMech.Ising
