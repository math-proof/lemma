module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
public import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[ext]
theorem LPReplicaPooledSelectedSlotState.ext
    {G : SimpleGraph V} {sites : I -> V}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {x y : LPReplicaPooledSelectedSlotState G sites q}
    (hprofile : x.profile = y.profile)
    (hselected : x.selected = y.selected)
    (hslots : x.slots = y.slots) : x = y := by
  cases x
  cases y
  cases hprofile
  cases hselected
  cases hslots
  rfl

end
end StatMech.Ising
