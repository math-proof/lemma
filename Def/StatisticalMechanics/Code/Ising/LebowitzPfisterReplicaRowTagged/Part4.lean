/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

def lpReplicaRowComponent (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) (root : LPReplicaCurrentVertex V) :
    Finset (LPReplicaCurrentVertex V) :=
  RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaRowCopies G sites m tag row) root

end
end StatMech.Ising
