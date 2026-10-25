/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCoupledPairedSource_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ m ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagDecoratedSourcesAtProfile G sites i j q m).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagDecoratedSourcesAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
      intro z hz
      unfold lpReplicaOffdiagCoupledPairedRelevantProfiles
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨z, hz, rfl⟩))

theorem lpReplicaOffdiagCoupledPairedOutputs_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card =
      ∑ m ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagCoupledPairedOutputsAtProfile
          G sites i j q m).card := by
  classical
  simpa only [lpReplicaOffdiagCoupledPairedOutputsAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
      intro y hy
      unfold lpReplicaOffdiagCoupledPairedRelevantProfiles
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨y, hy, rfl⟩))


end
end StatMech.Ising
