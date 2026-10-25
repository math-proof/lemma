/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part11
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)
        (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c) = c.1 := by
  classical
  let C := lpReplicaProfileCopyEquivOrbitCoord G sites m
  let Q := lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L
  let d := C c
  have hedge : (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm d.1 = c.1 :=
    lpReplicaProfileCopyEquivOrbitCoord_edge G sites m c
  change lpReplicaOrbitFourColorSlotEdge G sites q
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)
      (Q d) = c.1
  rcases d with ⟨fixed | strict, k⟩
  · rw [lpReplicaOrbitProfileCoordEquivCommonSlot_fixed]
    change fixed.1 = c.1
    simpa using hedge
  · rcases strict with rep | reflected
    · rw [lpReplicaOrbitProfileCoordEquivCommonSlot_strict]
      rw [lpReplicaOrbitFourColorSlotEdge]
      simp only [lpReplicaOrbitFourColorSlotStateOfTag_allocation,
        lpReplicaProfileOrbitPairedCoordEquivSlot_apply_left_mem, ↓reduceIte]
      simpa using hedge
    · rw [lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict]
      rw [lpReplicaOrbitFourColorSlotEdge]
      simp only [lpReplicaOrbitFourColorSlotStateOfTag_allocation,
        lpReplicaProfileOrbitPairedCoordEquivSlot_apply_right_not_mem,
        ↓reduceIte]
      simpa using hedge


end
end StatMech.Ising
