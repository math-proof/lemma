/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[ext]
theorem LPReplicaProfileOrbitSlotState.ext
    {G : SimpleGraph V} {sites : I -> V}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {s t : LPReplicaProfileOrbitSlotState G sites q}
    (ha : s.allocation = t.allocation)
    (hr : s.selectedRep = t.selectedRep)
    (ht : s.selectedReflect = t.selectedReflect) : s = t := by
  cases s
  cases t
  cases ha
  cases hr
  cases ht
  rfl


end
end StatMech.Ising
