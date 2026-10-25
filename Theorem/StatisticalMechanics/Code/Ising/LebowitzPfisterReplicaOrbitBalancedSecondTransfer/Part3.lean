/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplica_map_symmDiff
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X ↪ Y) (A B : Finset X) :
    (A ∆ B).map f = A.map f ∆ B.map f := by
  change ((A \ B) ∪ (B \ A)).map f =
    (A.map f \ B.map f) ∪ (B.map f \ A.map f)
  rw [Finset.map_union, Finset.map_sdiff, Finset.map_sdiff]

theorem lpReplicaCurrentReflect_seam_symmDiff_ghost
    (G : SimpleGraph V) (sites : I -> V) (i : I) :
    (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1).map
        lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
  rw [lpReplica_map_symmDiff,
    lpReplicaCurrentReflect_seamSource G sites i,
    lpReplicaCurrentReflect_ghostSource G sites]


end
end StatMech.Ising
