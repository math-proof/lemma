/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaTagEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part5
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaTagEquiv
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaTransportTag
    (G : SimpleGraph V) (sites : I -> V)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (E : Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites) n)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Copy (lpReplicaCurrentGraph G sites) n -> LPReplicaRowTag :=
  fun c => tag (E.symm c)


end
end StatMech.Ising
