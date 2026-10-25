/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaCollisionSplitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  ↑((Finset.univ : Finset
      (Finset (Copy (lpReplicaCurrentGraph G sites) m))).filter fun S =>
        profileFlux (lpReplicaCurrentGraph G sites) m S = K)

end
end StatMech.Ising
