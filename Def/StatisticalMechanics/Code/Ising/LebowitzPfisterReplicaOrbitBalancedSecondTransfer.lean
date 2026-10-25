/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaBalancedComponentSelector
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Finset (Copy (lpReplicaCurrentGraph G sites) m) :=
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  edgeComponent e K0
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∪
    edgeComponent e K1
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)

end
end StatMech.Ising
