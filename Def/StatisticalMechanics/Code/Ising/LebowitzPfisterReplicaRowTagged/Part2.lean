/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

section CollisionTag

variable [Fintype I] [DecidableEq I]


def lpReplicaCollisionRowTag
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)) :
    Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites a b) -> LPReplicaRowTag :=
  fun c =>
    if c ∈ (Finset.univ : Finset
        (Copy (lpReplicaCurrentGraph G sites) a)).map
          (lpReplicaCollisionLeftCopyEmbedding G sites a b) then
      (false, if c ∈ Sa.map
        (lpReplicaCollisionLeftCopyEmbedding G sites a b) then false else true)
    else
      (true, if c ∈ Sb.map
        (lpReplicaCollisionRightCopyEmbedding G sites a b) then false else true)

end CollisionTag
end
end StatMech.Ising
