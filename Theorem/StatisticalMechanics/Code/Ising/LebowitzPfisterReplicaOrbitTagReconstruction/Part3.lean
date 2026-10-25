/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitTagReconstruction.Part2
open Finset


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaTaggedRowBackEmbedding_ends
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool)
    (c : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaTaggedRowProfile G sites m tag row)) :
    endsM (lpReplicaCurrentGraph G sites) m
        (lpReplicaTaggedRowBackEmbedding G sites m tag row c) =
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaTaggedRowProfile G sites m tag row) c := by
  let E := lpReplicaCopySubsetEquivProfile G sites m
    (lpReplicaRowCopies G sites m tag row)
  have h := lpReplicaCopySubsetEquivProfile_ends G sites m
    (lpReplicaRowCopies G sites m tag row) (E.symm c)
  simpa only [E, lpReplicaTaggedRowBackEmbedding,
    Equiv.apply_symm_apply] using h.symm


end
end StatMech.Ising
